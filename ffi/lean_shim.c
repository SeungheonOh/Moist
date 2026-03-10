// Lean runtime shim: exposes inline functions from lean.h as real symbols
// so they can be linked from the Zig FFI library.
#include <lean/lean.h>

LEAN_EXPORT lean_obj_res lean_shim_alloc_sarray(unsigned elem_size, size_t size, size_t capacity) {
    return lean_alloc_sarray(elem_size, size, capacity);
}

LEAN_EXPORT uint8_t* lean_shim_sarray_cptr(lean_object * o) {
    return lean_sarray_cptr(o);
}

LEAN_EXPORT size_t lean_shim_sarray_size(b_lean_obj_arg o) {
    return lean_sarray_size(o);
}

LEAN_EXPORT lean_obj_res lean_shim_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    return lean_alloc_ctor(tag, num_objs, scalar_sz);
}

LEAN_EXPORT void lean_shim_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v) {
    lean_ctor_set(o, i, v);
}

LEAN_EXPORT lean_object * lean_shim_box(size_t n) {
    return lean_box(n);
}

LEAN_EXPORT lean_obj_res lean_shim_box_uint64(uint64_t v) {
    return lean_box_uint64(v);
}

LEAN_EXPORT lean_obj_res lean_shim_io_result_mk_ok(lean_obj_arg a) {
    return lean_io_result_mk_ok(a);
}
