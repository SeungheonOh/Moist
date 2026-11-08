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

// ---------------------------------------------------------------------------
// Cryptographic primitives behind the Lean model's opaque builtins
// (Moist/CEK/OpaqueBuiltins.lean). The Lean kernel never sees these: the
// model's semantics for hashes, signatures and BLS12-381 are `opaque`, and
// these functions are only their runtime implementations.
//
// Every function returns a ByteArray whose first byte is a status:
//   0 = the builtin fails, 1 = success followed by the result bytes.
// ---------------------------------------------------------------------------

const blst = plutuz.crypto.blst;

fn leanBytes(o: b_lean_obj_arg) []const u8 {
    return lean_sarray_cptr(o)[0..lean_sarray_size(o)];
}

fn statusFail() lean_obj_res {
    return mkLeanByteArray(&[_]u8{0});
}

fn statusOk(data: []const u8) lean_obj_res {
    const ba = lean_alloc_sarray(1, data.len + 1, data.len + 1);
    const dst = lean_sarray_cptr(ba);
    dst[0] = 1;
    @memcpy(dst[1 .. data.len + 1], data);
    return ba;
}

fn statusBool(b: bool) lean_obj_res {
    return statusOk(&[_]u8{if (b) 1 else 0});
}

/// Hashes: 0 sha2_256, 1 sha3_256, 2 blake2b_224, 3 blake2b_256, 4 keccak_256, 5 ripemd_160.
export fn moist_crypto_hash(code: u8, input: b_lean_obj_arg) lean_obj_res {
    const bytes = leanBytes(input);
    switch (code) {
        0 => {
            var out: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(bytes, &out, .{});
            return statusOk(&out);
        },
        1 => {
            var out: [32]u8 = undefined;
            std.crypto.hash.sha3.Sha3_256.hash(bytes, &out, .{});
            return statusOk(&out);
        },
        2 => {
            var out: [28]u8 = undefined;
            std.crypto.hash.blake2.Blake2b(224).hash(bytes, &out, .{});
            return statusOk(&out);
        },
        3 => {
            var out: [32]u8 = undefined;
            std.crypto.hash.blake2.Blake2b256.hash(bytes, &out, .{});
            return statusOk(&out);
        },
        4 => {
            var out: [32]u8 = undefined;
            std.crypto.hash.sha3.Keccak256.hash(bytes, &out, .{});
            return statusOk(&out);
        },
        5 => {
            var out: [20]u8 = undefined;
            plutuz.crypto.ripemd160.Ripemd160.hash(bytes, &out, .{});
            return statusOk(&out);
        },
        else => return statusFail(),
    }
}

fn verifyEd25519(public_key: []const u8, message: []const u8, signature: []const u8) lean_obj_res {
    if (public_key.len != 32) return statusFail();
    if (signature.len != 64) return statusFail();
    const pk = std.crypto.sign.Ed25519.PublicKey.fromBytes(public_key[0..32].*) catch {
        return statusBool(false);
    };
    const sig = std.crypto.sign.Ed25519.Signature.fromBytes(signature[0..64].*);
    sig.verify(message, pk) catch return statusBool(false);
    return statusBool(true);
}

fn verifyEcdsa(public_key: []const u8, message: []const u8, signature: []const u8) lean_obj_res {
    if (public_key.len != 33) return statusFail();
    if (message.len != 32) return statusFail();
    if (signature.len != 64) return statusFail();
    const Ecdsa = std.crypto.sign.ecdsa.EcdsaSecp256k1Sha256;
    const pk = Ecdsa.PublicKey.fromSec1(public_key) catch return statusFail();
    const group_order = [32]u8{
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
        0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B,
        0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
    };
    const zero = [_]u8{0} ** 32;
    const r_bytes = signature[0..32];
    const s_bytes = signature[32..64];
    if (std.mem.eql(u8, r_bytes, &zero) or std.mem.order(u8, r_bytes, &group_order) != .lt) return statusFail();
    if (std.mem.eql(u8, s_bytes, &zero) or std.mem.order(u8, s_bytes, &group_order) != .lt) return statusFail();
    const half_order = [32]u8{
        0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x5D, 0x57, 0x6E, 0x73, 0x57, 0xA4, 0x50, 0x1D,
        0xDF, 0xE9, 0x2F, 0x46, 0x68, 0x1B, 0x20, 0xA0,
    };
    if (std.mem.order(u8, s_bytes, &half_order) == .gt) return statusBool(false);
    const sig = Ecdsa.Signature.fromBytes(signature[0..64].*);
    sig.verifyPrehashed(message[0..32].*, pk) catch return statusBool(false);
    return statusBool(true);
}

fn verifySchnorr(public_key: []const u8, message: []const u8, signature: []const u8) lean_obj_res {
    if (public_key.len != 32) return statusFail();
    if (signature.len != 64) return statusFail();
    const Secp256k1 = std.crypto.ecc.Secp256k1;
    const Fe = Secp256k1.Fe;
    const Sha256 = std.crypto.hash.sha2.Sha256;
    const pk_x = Fe.fromBytes(public_key[0..32].*, .big) catch return statusFail();
    const pk_y = Secp256k1.recoverY(pk_x, false) catch return statusFail();
    const P = Secp256k1{ .x = pk_x, .y = pk_y };
    const r_bytes = signature[0..32];
    const s_bytes = signature[32..64];
    const tag_hash = [32]u8{
        0x7b, 0xb5, 0x2d, 0x7a, 0x9f, 0xef, 0x58, 0x32,
        0x3e, 0xb1, 0xbf, 0x7a, 0x40, 0x7d, 0xb3, 0x82,
        0xd2, 0xf3, 0xf2, 0xd8, 0x1b, 0xb1, 0x22, 0x4f,
        0x49, 0xfe, 0x51, 0x8f, 0x6d, 0x48, 0xd3, 0x7c,
    };
    var challenge_hash: [32]u8 = undefined;
    var hasher = Sha256.init(.{});
    hasher.update(&tag_hash);
    hasher.update(&tag_hash);
    hasher.update(r_bytes);
    hasher.update(public_key);
    hasher.update(message);
    hasher.final(&challenge_hash);
    const e = Secp256k1.scalar.Scalar.fromBytes(challenge_hash, .big) catch return statusBool(false);
    const s = Secp256k1.scalar.Scalar.fromBytes(s_bytes.*, .big) catch return statusBool(false);
    const sG = Secp256k1.basePoint.mul(s.toBytes(.little), .little) catch return statusBool(false);
    const eP = P.mul(e.toBytes(.little), .little) catch return statusBool(false);
    const R = sG.sub(eP);
    const R_affine = R.affineCoordinates();
    if (R_affine.y.isOdd()) return statusBool(false);
    const R_x_bytes = R_affine.x.toBytes(.big);
    if (!std.mem.eql(u8, &R_x_bytes, r_bytes)) return statusBool(false);
    return statusBool(true);
}

/// Signatures: 0 Ed25519, 1 ECDSA secp256k1, 2 Schnorr secp256k1.
export fn moist_crypto_verify(code: u8, pk: b_lean_obj_arg, msg: b_lean_obj_arg, sig: b_lean_obj_arg) lean_obj_res {
    const p = leanBytes(pk);
    const m = leanBytes(msg);
    const s = leanBytes(sig);
    return switch (code) {
        0 => verifyEd25519(p, m, s),
        1 => verifyEcdsa(p, m, s),
        2 => verifySchnorr(p, m, s),
        else => statusFail(),
    };
}

fn g1Of(bytes: []const u8) ?blst.P1 {
    if (bytes.len != blst.BLST_P1_COMPRESSED_SIZE) return null;
    return blst.uncompressG1(bytes[0..blst.BLST_P1_COMPRESSED_SIZE]) catch null;
}

fn g2Of(bytes: []const u8) ?blst.P2 {
    if (bytes.len != blst.BLST_P2_COMPRESSED_SIZE) return null;
    return blst.uncompressG2(bytes[0..blst.BLST_P2_COMPRESSED_SIZE]) catch null;
}

fn okG1(p: blst.P1) lean_obj_res {
    const c = blst.compressG1(&p);
    return statusOk(&c);
}

fn okG2(p: blst.P2) lean_obj_res {
    const c = blst.compressG2(&p);
    return statusOk(&c);
}

fn fp12Of(bytes: []const u8) ?blst.Fp12 {
    var out: blst.Fp12 = undefined;
    const dst = std.mem.asBytes(&out);
    if (bytes.len != dst.len) return null;
    @memcpy(dst, bytes);
    return out;
}

fn okFp12(x: blst.Fp12) lean_obj_res {
    return statusOk(std.mem.asBytes(&x));
}

/// BLS12-381 operations on canonical compressed points (G1: 48 bytes, G2: 96 bytes)
/// and raw Miller-loop results. Scalars are passed as 32-byte little-endian
/// integers already reduced modulo the group order.
///   0 g1 add(a, b)          1 g1 neg(a)            2 g1 scalarMul(scalar a, point b)
///   3 g1 equal(a, b)        4 g1 hashToGroup(msg a, dst b)   5 g1 uncompress(a)
///   10..15: the same for G2
///   20 millerLoop(g1 a, g2 b)   21 mulMlResult(a, b)   22 finalVerify(a, b)
export fn moist_crypto_bls(op: u8, a_obj: b_lean_obj_arg, b_obj: b_lean_obj_arg) lean_obj_res {
    const a = leanBytes(a_obj);
    const b = leanBytes(b_obj);
    switch (op) {
        0 => {
            const p = g1Of(a) orelse return statusFail();
            const q = g1Of(b) orelse return statusFail();
            return okG1(blst.addG1(&p, &q));
        },
        1 => {
            const p = g1Of(a) orelse return statusFail();
            return okG1(blst.negG1(&p));
        },
        2 => {
            if (a.len != 32) return statusFail();
            const p = g1Of(b) orelse return statusFail();
            return okG1(blst.scalarMulG1(&p, a, 256));
        },
        3 => {
            const p = g1Of(a) orelse return statusFail();
            const q = g1Of(b) orelse return statusFail();
            return statusBool(blst.equalG1(&p, &q));
        },
        4 => {
            if (b.len > 255) return statusFail();
            return okG1(blst.hashToG1(a, b));
        },
        5 => {
            const p = g1Of(a) orelse return statusFail();
            return okG1(p);
        },
        10 => {
            const p = g2Of(a) orelse return statusFail();
            const q = g2Of(b) orelse return statusFail();
            return okG2(blst.addG2(&p, &q));
        },
        11 => {
            const p = g2Of(a) orelse return statusFail();
            return okG2(blst.negG2(&p));
        },
        12 => {
            if (a.len != 32) return statusFail();
            const p = g2Of(b) orelse return statusFail();
            return okG2(blst.scalarMulG2(&p, a, 256));
        },
        13 => {
            const p = g2Of(a) orelse return statusFail();
            const q = g2Of(b) orelse return statusFail();
            return statusBool(blst.equalG2(&p, &q));
        },
        14 => {
            if (b.len > 255) return statusFail();
            return okG2(blst.hashToG2(a, b));
        },
        15 => {
            const p = g2Of(a) orelse return statusFail();
            return okG2(p);
        },
        20 => {
            const p = g1Of(a) orelse return statusFail();
            const q = g2Of(b) orelse return statusFail();
            return okFp12(blst.millerLoop(&p, &q));
        },
        21 => {
            const x = fp12Of(a) orelse return statusFail();
            const y = fp12Of(b) orelse return statusFail();
            return okFp12(blst.mulFp12(&x, &y));
        },
        22 => {
            const x = fp12Of(a) orelse return statusFail();
            const y = fp12Of(b) orelse return statusFail();
            return statusBool(blst.finalVerify(&x, &y));
        },
        else => return statusFail(),
    }
}
