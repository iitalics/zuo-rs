use std::ffi::{c_void, c_longlong, c_char};

#[repr(transparent)]
#[allow(non_camel_case_types)]
/// Raw Zuo values.
pub struct zuo_ext_t {
    _opaque: c_void,
}

extern "C" {
    pub fn zuo_ext_primitive_init();
    pub fn zuo_ext_image_init(boot_image_file: *const c_char);
    pub fn zuo_ext_false() -> *const zuo_ext_t;
    pub fn zuo_ext_true() -> *const zuo_ext_t;
    pub fn zuo_ext_null() -> *const zuo_ext_t;
    pub fn zuo_ext_void() -> *const zuo_ext_t;
    pub fn zuo_ext_eof() -> *const zuo_ext_t;
    pub fn zuo_ext_empty_hash() -> *const zuo_ext_t;
    pub fn zuo_ext_integer(i: c_longlong) -> *const zuo_ext_t;
    pub fn zuo_ext_integer_value(v: *const zuo_ext_t) -> c_longlong;
    pub fn zuo_ext_cons(car: *const zuo_ext_t, cdr: *const zuo_ext_t) -> *const zuo_ext_t;
    pub fn zuo_ext_car(obj: *const zuo_ext_t) -> *const zuo_ext_t;
    pub fn zuo_ext_cdr(obj: *const zuo_ext_t) -> *const zuo_ext_t;
    pub fn zuo_ext_string(s: *const c_char, len: c_longlong) -> *const zuo_ext_t;
    pub fn zuo_ext_string_length(s: *const zuo_ext_t) -> c_longlong;
    pub fn zuo_ext_string_ptr(s: *const zuo_ext_t) -> *mut c_char;
    pub fn zuo_ext_symbol(s: *const c_char) -> *const zuo_ext_t;
    pub fn zuo_ext_hash_ref(ht: *const zuo_ext_t, key: *const zuo_ext_t, fail: *const zuo_ext_t) -> *const zuo_ext_t;
    pub fn zuo_ext_hash_set(ht: *const zuo_ext_t, key: *const zuo_ext_t, val: *const zuo_ext_t) -> *const zuo_ext_t;
    pub fn zuo_ext_kernel_env() -> *const zuo_ext_t;
    pub fn zuo_ext_apply(proc: *const zuo_ext_t, args: *const zuo_ext_t) -> *const zuo_ext_t;
    pub fn zuo_ext_runtime_init(lib_path: *const zuo_ext_t, runtime_env: *const zuo_ext_t);
    pub fn zuo_ext_eval_module(as_module_path: *const zuo_ext_t, content: *const c_char, len: c_longlong) -> *const zuo_ext_t;
    pub fn zuo_ext_stash_push(v: *const zuo_ext_t);
    pub fn zuo_ext_stash_pop() -> *const zuo_ext_t;
}
