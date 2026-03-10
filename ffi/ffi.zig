//! FFI bridge between Lean 4 and Plutuz CEK machine.
//!
//! Exports C-ABI functions that operate directly on Lean objects (ByteArray, etc.)
//! Uses manual extern declarations for the Lean C API instead of @cImport,
//! since lean.h contains macros/inline functions that don't translate cleanly.

const std = @import("std");
const plutuz = @import("plutuz");

// Use page_allocator wrapped in an arena for each eval call.
const page_alloc = std.heap.page_allocator;

// ---------------------------------------------------------------------------
// Lean C API declarations (subset needed for FFI)
// ---------------------------------------------------------------------------

const lean_object = opaque {};
const lean_obj_arg = ?*lean_object;
const b_lean_obj_arg = ?*lean_object;
const lean_obj_res = ?*lean_object;

// lean.h scalar array (ByteArray) layout:
//   lean_object header (16 bytes on 64-bit)
//   size_t m_size
//   size_t m_capacity
//   uint8_t m_data[]
//
// We use the C API functions to access these.

// These are shim functions (lean_shim.c) wrapping lean.h inline functions.
extern fn lean_shim_alloc_sarray(elem_size: c_uint, size: usize, capacity: usize) lean_obj_res;
extern fn lean_shim_sarray_cptr(o: b_lean_obj_arg) [*]u8;
extern fn lean_shim_sarray_size(o: b_lean_obj_arg) usize;
extern fn lean_shim_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) lean_obj_res;
extern fn lean_shim_ctor_set(o: lean_obj_arg, i: c_uint, v: lean_obj_arg) void;
extern fn lean_shim_box(n: usize) lean_obj_res;
extern fn lean_shim_box_uint64(n: u64) lean_obj_res;
extern fn lean_shim_io_result_mk_ok(a: lean_obj_arg) lean_obj_res;
// lean_mk_string_from_bytes is a real LEAN_EXPORT symbol (not inline).
extern fn lean_mk_string_from_bytes(s: [*]const u8, len: usize) lean_obj_res;

// Convenience aliases to keep call sites clean.
const lean_alloc_sarray = lean_shim_alloc_sarray;
const lean_sarray_cptr = lean_shim_sarray_cptr;
const lean_sarray_size = lean_shim_sarray_size;
const lean_alloc_ctor = lean_shim_alloc_ctor;
const lean_ctor_set = lean_shim_ctor_set;
const lean_box = lean_shim_box;
const lean_box_uint64 = lean_shim_box_uint64;
const lean_io_result_mk_ok = lean_shim_io_result_mk_ok;

// ---------------------------------------------------------------------------
// Error codes (matching Lean CEKError inductive, 0-indexed)
// ---------------------------------------------------------------------------

const ErrCode = enum(u32) {
    success = 0,
    out_of_budget = 1,
    unbound_variable = 2,
    type_mismatch = 3,
    non_functional_application = 4,
    non_constr_scrutinee = 5,
    missing_case_branch = 6,
    builtin_error = 7,
    builtin_term_argument_expected = 8,
    non_polymorphic_instantiation = 9,
    unexpected_builtin_term_argument = 10,
    open_term_evaluated = 11,
    out_of_memory = 12,
    decode_error = 13,
    encode_error = 14,
    unknown = 15,
};

fn machineErrorToCode(err: anyerror) ErrCode {
    return switch (err) {
        error.OutOfBudget => .out_of_budget,
        error.UnboundVariable => .unbound_variable,
        error.TypeMismatch => .type_mismatch,
        error.NonFunctionalApplication => .non_functional_application,
        error.NonConstrScrutinee => .non_constr_scrutinee,
        error.MissingCaseBranch => .missing_case_branch,
        error.BuiltinError => .builtin_error,
        error.BuiltinTermArgumentExpected => .builtin_term_argument_expected,
        error.NonPolymorphicInstantiation => .non_polymorphic_instantiation,
        error.UnexpectedBuiltinTermArgument => .unexpected_builtin_term_argument,
        error.OpenTermEvaluated => .open_term_evaluated,
        error.OutOfMemory => .out_of_memory,
        error.EndOfInput,
        error.InvalidFiller,
        error.InvalidTag,
        error.InvalidConstantTag,
        error.InvalidBuiltinTag,
        error.UnknownTypeTag,
        error.Utf8Invalid,
        error.CborDecodeError,
        => .decode_error,
        else => .unknown,
    };
}

// ---------------------------------------------------------------------------
// Lean object helpers
// ---------------------------------------------------------------------------

fn mkLeanByteArray(data: []const u8) lean_obj_res {
    const ba = lean_alloc_sarray(1, data.len, data.len);
    const dst = lean_sarray_cptr(ba);
    @memcpy(dst[0..data.len], data);
    return ba;
}

/// Build Lean result: (UInt32 × (UInt64 × (UInt64 × ByteArray)))
/// All scalars boxed, nested right-associated Prod.
fn mkResult(err_code: ErrCode, cpu: u64, mem: u64, payload: lean_obj_res) lean_obj_res {
    // Innermost: Prod.mk mem payload
    const pair3 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair3, 0, lean_box_uint64(mem));
    lean_ctor_set(pair3, 1, payload);

    // Middle: Prod.mk cpu pair3
    const pair2 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair2, 0, lean_box_uint64(cpu));
    lean_ctor_set(pair2, 1, pair3);

    // Outer: Prod.mk errCode pair2
    const pair1 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair1, 0, lean_box(@intFromEnum(err_code)));
    lean_ctor_set(pair1, 1, pair2);

    return lean_io_result_mk_ok(pair1);
}

// ---------------------------------------------------------------------------
// Exported FFI function
// ---------------------------------------------------------------------------

/// Evaluate flat-encoded UPLC bytes with budget limits.
///
/// Lean signature:
///   @[extern "lean_plutuz_eval_flat"]
///   opaque evalFlatRaw (program : @& ByteArray) (cpuBudget : UInt64) (memBudget : UInt64)
///       : IO (UInt32 × UInt64 × UInt64 × ByteArray)
///
/// Returns (errCode, cpuUsed, memUsed, payload) where:
///   errCode = 0  -> payload is flat-encoded result program
///   errCode > 0  -> payload is UTF-8 error name
export fn lean_plutuz_eval_flat(
    program: b_lean_obj_arg,
    cpu_budget: u64,
    mem_budget: u64,
) lean_obj_res {
    // Set up arena allocator for this call
    var arena = std.heap.ArenaAllocator.init(page_alloc);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Extract bytes from Lean ByteArray
    const data_ptr = lean_sarray_cptr(program);
    const data_len = lean_sarray_size(program);
    const bytes = data_ptr[0..data_len];

    // 1. Decode flat -> DeBruijnProgram
    const prog = plutuz.decodeFlatDeBruijn(alloc, bytes) catch |err| {
        const msg = @errorName(err);
        return mkResult(machineErrorToCode(err), 0, 0, mkLeanByteArray(msg));
    };

    // 2. Set up machine with budget
    const initial_budget = plutuz.cek.ExBudget{
        .cpu = @intCast(cpu_budget),
        .mem = @intCast(mem_budget),
    };
    var machine = plutuz.DeBruijnMachine.init(alloc);
    machine.budget = initial_budget;
    machine.restricting = true;
    machine.semantics = .c; // V3+ semantics

    // 3. Evaluate
    const result_term = machine.run(prog.term) catch |err| {
        const consumed = machine.consumedBudget(initial_budget);
        const cpu_used: u64 = @intCast(@max(0, consumed.cpu));
        const mem_used: u64 = @intCast(@max(0, consumed.mem));
        const msg = @errorName(err);
        return mkResult(machineErrorToCode(err), cpu_used, mem_used, mkLeanByteArray(msg));
    };

    // 4. Get consumed budget
    const consumed = machine.consumedBudget(initial_budget);
    const cpu_used: u64 = @intCast(@max(0, consumed.cpu));
    const mem_used: u64 = @intCast(@max(0, consumed.mem));

    // 5. Wrap result term in a Program and encode to flat
    const result_prog = alloc.create(plutuz.DeBruijnProgram) catch {
        return mkResult(.out_of_memory, cpu_used, mem_used, mkLeanByteArray("OutOfMemory"));
    };
    result_prog.* = .{
        .version = prog.version,
        .term = result_term,
    };

    const result_bytes = plutuz.encodeFlatDeBruijn(alloc, result_prog) catch |err| {
        const msg = @errorName(err);
        return mkResult(machineErrorToCode(err), cpu_used, mem_used, mkLeanByteArray(msg));
    };

    // 6. Return success
    return mkResult(.success, cpu_used, mem_used, mkLeanByteArray(result_bytes));
}
