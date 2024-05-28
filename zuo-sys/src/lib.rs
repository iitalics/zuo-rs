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
    pub fn zuo_ext_false() -> *mut zuo_ext_t;
    pub fn zuo_ext_true() -> *mut zuo_ext_t;
    pub fn zuo_ext_null() -> *mut zuo_ext_t;
    pub fn zuo_ext_void() -> *mut zuo_ext_t;
    pub fn zuo_ext_eof() -> *mut zuo_ext_t;
    pub fn zuo_ext_empty_hash() -> *mut zuo_ext_t;
    pub fn zuo_ext_integer(i: c_longlong) -> *mut zuo_ext_t;
    pub fn zuo_ext_integer_value(v: *mut zuo_ext_t) -> c_longlong;
    pub fn zuo_ext_cons(car: *mut zuo_ext_t, cdr: *mut zuo_ext_t) -> *mut zuo_ext_t;
    pub fn zuo_ext_car(obj: *mut zuo_ext_t) -> *mut zuo_ext_t;
    pub fn zuo_ext_cdr(obj: *mut zuo_ext_t) -> *mut zuo_ext_t;
    pub fn zuo_ext_string(s: *const c_char, len: c_longlong) -> *mut zuo_ext_t;
    pub fn zuo_ext_string_length(s: *mut zuo_ext_t) -> c_longlong;
    pub fn zuo_ext_string_ptr(s: *mut zuo_ext_t) -> *mut c_char;
    pub fn zuo_ext_symbol(s: *const c_char) -> *mut zuo_ext_t;
    pub fn zuo_ext_hash_ref(ht: *mut zuo_ext_t, key: *mut zuo_ext_t, fail: *mut zuo_ext_t) -> *mut zuo_ext_t;
    pub fn zuo_ext_hash_set(ht: *mut zuo_ext_t, key: *mut zuo_ext_t, val: *mut zuo_ext_t) -> *mut zuo_ext_t;
    pub fn zuo_ext_kernel_env() -> *mut zuo_ext_t;
    pub fn zuo_ext_apply(proc: *mut zuo_ext_t, args: *mut zuo_ext_t) -> *mut zuo_ext_t;
    pub fn zuo_ext_runtime_init(lib_path: *mut zuo_ext_t, runtime_env: *mut zuo_ext_t);
    pub fn zuo_ext_eval_module(as_module_path: *mut zuo_ext_t, content: *const c_char, len: c_longlong) -> *mut zuo_ext_t;
    pub fn zuo_ext_stash_push(v: *mut zuo_ext_t);
    pub fn zuo_ext_stash_pop() -> *mut zuo_ext_t;
}
