use std::cell::{Cell, RefCell};
use std::ffi::CStr;
use std::path::{Path, PathBuf};
use std::rc::{Rc, Weak};
use std::sync::atomic;
use std::{fmt, ptr};

pub use zuo_sys::zuo_ext_t;

/// Handle to the global Zuo interpreter.
pub struct Zuo {
    stash: RefCell<Vec<WeakRoot>>,
    stash_temp: RefCell<Vec<Root>>,
}

impl Zuo {
    /// Returns a builder object for configuring the initialization of the interpreter.
    pub fn builder() -> ZuoBuilder {
        ZuoBuilder::new()
    }

    /// Initializes the interpreter with all default settings. This means that no library
    /// path is set, so you will not be able to load modules from the filesystem.
    pub fn init() -> Option<Self> {
        Self::builder().init()
    }

    unsafe fn do_init(lib_path: Option<&Path>) -> Self {
        zuo_sys::zuo_ext_primitive_init();

        // TODO: init primitive functions

        let boot_image_file = ptr::null();
        zuo_sys::zuo_ext_image_init(boot_image_file);

        let lib_path = match lib_path {
            Some(path) => string(path.as_os_str().as_encoded_bytes()),
            None => zuo_sys::zuo_ext_false(),
        };

        // TODO: fill runtime-env

        let runtime_env = zuo_sys::zuo_ext_empty_hash();
        zuo_sys::zuo_ext_runtime_init(lib_path, runtime_env);

        Self {
            stash: RefCell::new(vec![]),
            stash_temp: RefCell::new(vec![]),
        }
    }

    // == integer ==

    /// Creates an integer value.
    pub fn integer(&self, v: i64) -> ZuoValue {
        let raw_v = unsafe { zuo_sys::zuo_ext_integer(v) };
        self.stash(raw_v)
    }

    /// Returns `true` if `v` is an integer.
    pub fn is_integer(&self, v: &ZuoValue) -> bool {
        unsafe { is_not_false(kernel_call(c"integer?", &[v.as_raw()])) }
    }

    /// Gets the integer value from `v` if it is an integer, returns `None` otherwise.
    pub fn get_integer(&self, v: &ZuoValue) -> Option<i64> {
        if !self.is_integer(v) {
            return None;
        }
        Some(unsafe { self.get_integer_unchecked(v) })
    }

    /// Gets the integer value from `v` without checking that it is an integer.
    ///
    /// # Safety
    ///
    /// - `v` must be an integer value.
    pub unsafe fn get_integer_unchecked(&self, v: &ZuoValue) -> i64 {
        zuo_sys::zuo_ext_integer_value(v.as_raw())
    }

    // == string ==

    /// Creates a string value from a given byte slice.
    pub fn string(&self, s: &[u8]) -> ZuoValue {
        let raw_v = unsafe { string(s) };
        self.stash(raw_v)
    }

    /// Returns `true` if `v` is a string.
    pub fn is_string(&self, v: &ZuoValue) -> bool {
        unsafe { is_not_false(kernel_call(c"string?", &[v.as_raw()])) }
    }

    /// Gets the bytes contents from `v` if it is a string, returns `None` otherwise.
    pub fn get_string(&self, v: &ZuoValue) -> Option<Vec<u8>> {
        if !self.is_string(v) {
            return None;
        }
        Some(unsafe { self.get_string_unchecked(v) }.to_vec())
    }

    /// Gets the bytes contents from `v` if it is a string, decoding it as UTF-8. If it is
    /// not a string or if the string is not a valid UTF-8 sequence, returns `None`.
    pub fn get_string_utf8(&self, v: &ZuoValue) -> Option<String> {
        if !self.is_string(v) {
            return None;
        }
        match std::str::from_utf8(unsafe { self.get_string_unchecked(v) }) {
            Ok(s) => Some(s.to_owned()),
            Err(_) => None,
        }
    }

    /// Gets the bytes contents from `v` if it is a string, decoding it as UTF-8. If it is
    /// not a string, returns `None`. If it is not a valid UTF-8 sequence, lossily
    /// converts it to one using [`String::from_utf8_lossy`].
    pub fn get_string_utf8_lossy(&self, v: &ZuoValue) -> Option<String> {
        if !self.is_string(v) {
            return None;
        }
        Some(String::from_utf8_lossy(unsafe { self.get_string_unchecked(v) }).into())
    }

    /// Gets the bytes contents from `v` without checking that it is a string.
    ///
    /// # Safety
    ///
    /// - `v` must be a string value. The resulting slice must not be used after garbage
    /// collection, which may occur from evaluating expressions.
    pub unsafe fn get_string_unchecked(&self, v: &ZuoValue) -> &[u8] {
        get_string(v.as_raw())
    }

    // == singletons ==
    // TODO: cache

    /// Returns a true or false value (`#t` or `#f` respectively).
    pub fn boolean(&self, b: bool) -> ZuoValue {
        let raw_v = if b {
            unsafe { zuo_sys::zuo_ext_true() }
        } else {
            unsafe { zuo_sys::zuo_ext_false() }
        };
        self.stash(raw_v)
    }

    /// Returns `true` if `v` is identical to the true value, `#t`.
    pub fn is_true(&self, v: &ZuoValue) -> bool {
        *v == unsafe { zuo_sys::zuo_ext_true() }
    }

    /// Returns `true` if `v` is identical to the false value, `#f`.
    pub fn is_false(&self, v: &ZuoValue) -> bool {
        *v == unsafe { zuo_sys::zuo_ext_false() }
    }

    /// Returns `true` if `v` is not identical to the false value. This essentially
    /// determines the "truth value" of `v`, in other words equivalent to the Zuo
    /// expression `(if v #t #f)`.
    pub fn is_not_false(&self, v: &ZuoValue) -> bool {
        *v != unsafe { zuo_sys::zuo_ext_false() }
    }

    /// Returns the null value, `'()`, also known as the empty list.
    pub fn null(&self) -> ZuoValue {
        self.stash(unsafe { zuo_sys::zuo_ext_null() })
    }

    /// Returns `true` if `v` is identical to the null value.
    pub fn is_null(&self, v: &ZuoValue) -> bool {
        *v == unsafe { zuo_sys::zuo_ext_null() }
    }

    /// Returns the void value, `(void)`.
    pub fn void(&self) -> ZuoValue {
        self.stash(unsafe { zuo_sys::zuo_ext_void() })
    }

    /// Returns `true` if `v` is identical to the void value.
    pub fn is_void(&self, v: &ZuoValue) -> bool {
        *v == unsafe { zuo_sys::zuo_ext_void() }
    }

    /// Returns the EOF value, `eof`.
    pub fn eof(&self) -> ZuoValue {
        self.stash(unsafe { zuo_sys::zuo_ext_eof() })
    }

    /// Returns `true` if `v` is identical to the EOF value.
    pub fn is_eof(&self, v: &ZuoValue) -> bool {
        *v == unsafe { zuo_sys::zuo_ext_eof() }
    }

    // == symbol ==

    /// Creates a symbol value from the given C-string.
    pub fn symbol(&self, s: &CStr) -> ZuoValue {
        self.stash(unsafe { symbol(s) })
    }

    /// Returns `true` if `v` is a symbol.
    pub fn is_symbol(&self, v: &ZuoValue) -> bool {
        unsafe { is_not_false(kernel_call(c"symbol?", &[v.as_raw()])) }
    }

    /// Returns `true` if `lhs` is identical to the symbol given by the C-string `rhs`.
    pub fn eq_symbol(&self, lhs: &ZuoValue, rhs: &CStr) -> bool {
        *lhs == unsafe { symbol(rhs) }
    }

    // == pair ==

    /// Creates a pair from the given values.
    pub fn cons(&self, car: &ZuoValue, cdr: &ZuoValue) -> ZuoValue {
        let raw_v = unsafe { zuo_sys::zuo_ext_cons(car.as_raw(), cdr.as_raw()) };
        self.stash(raw_v)
    }

    /// Returns `true` if `v` is a pair.
    pub fn is_pair(&self, v: &ZuoValue) -> bool {
        unsafe { is_not_false(kernel_call(c"pair?", &[v.as_raw()])) }
    }

    /// Gets the head of the pair `v`, returns `None` if it is not a pair.
    pub fn car(&self, v: &ZuoValue) -> Option<ZuoValue> {
        if !self.is_pair(v) {
            return None;
        }
        Some(unsafe { self.car_unchecked(v) })
    }

    /// Gets the tail of the pair `v`, returns `None` if it is not a pair.
    pub fn cdr(&self, v: &ZuoValue) -> Option<ZuoValue> {
        if !self.is_pair(v) {
            return None;
        }
        Some(unsafe { self.cdr_unchecked(v) })
    }

    /// Gets the head of the pair `v` without checking that it is a pair.
    ///
    /// # Safety
    ///
    /// - `v` must be a pair value.
    pub unsafe fn car_unchecked(&self, v: &ZuoValue) -> ZuoValue {
        self.stash(unsafe { zuo_sys::zuo_ext_car(v.as_raw()) })
    }

    /// Gets the tail of the pair `v` without checking that it is a pair.
    ///
    /// # Safety
    ///
    /// - `v` must be a pair value.
    pub unsafe fn cdr_unchecked(&self, v: &ZuoValue) -> ZuoValue {
        self.stash(unsafe { zuo_sys::zuo_ext_cdr(v.as_raw()) })
    }

    /// Returns `true` if `v` is a proper list, meaning it must be a series of pairs
    /// followed by null. See Zuo function `list?`.
    pub fn is_list(&self, v: &ZuoValue) -> bool {
        unsafe { is_not_false(kernel_call(c"list?", &[v.as_raw()])) }
    }

    /// Returns the elements of the list `v`, or an empty vector if it isn't a proper
    /// list.
    pub fn get_list(&self, v: &ZuoValue) -> Vec<ZuoValue> {
        if !self.is_list(v) {
            // TODO: error?
            return vec![];
        }

        unsafe { ListIter::new(v.as_raw()) }
            .map(|v| self.stash(v))
            .collect()
    }

    // == hash ==

    /// Returns `true` if `v` is a hash.
    pub fn is_hash(&self, v: &ZuoValue) -> bool {
        unsafe { is_not_false(kernel_call(c"hash?", &[v.as_raw()])) }
    }

    /// Looks up `key` in the hash. If not present, returns `dflt`, or false if `dflt` is
    /// `None`. Returns `None` if `hash` is not a hash table.
    pub fn hash_ref(
        &self,
        hash: &ZuoValue,
        key: &ZuoValue,
        dflt: Option<&ZuoValue>,
    ) -> Option<ZuoValue> {
        if !self.is_hash(hash) {
            return None;
        }
        let hash = hash.as_raw();
        let key = key.as_raw();
        let dflt = dflt.map(ZuoValue::as_raw);
        Some(self.stash(unsafe { hash_ref(hash, key, dflt) }))
    }

    /// Looks up the symbol given by C-string `key` in the hash. This is the same as
    /// `hash_ref(hash, symbol(key), dflt)`.
    pub fn hash_ref_symbol(
        &self,
        hash: &ZuoValue,
        key: &CStr,
        dflt: Option<&ZuoValue>,
    ) -> Option<ZuoValue> {
        if !self.is_hash(hash) {
            return None;
        }
        let hash = hash.as_raw();
        let key = unsafe { symbol(key) };
        let dflt = dflt.map(ZuoValue::as_raw);
        Some(self.stash(unsafe { hash_ref(hash, key, dflt) }))
    }

    // == formatting ==

    /// Formats the value `v` as a string using the `~v` ("print") formatter.
    pub fn format_print(&self, v: &ZuoValue) -> String {
        let res = unsafe { get_string(kernel_call(c"~v", &[v.as_raw()])) };
        String::from_utf8_lossy(res).into()
    }

    /// Formats the value `v` as a string using the `~a` ("display") formatter.
    pub fn format_display(&self, v: &ZuoValue) -> String {
        let res = unsafe { get_string(kernel_call(c"~a", &[v.as_raw()])) };
        String::from_utf8_lossy(res).into()
    }

    /// Formats the value `v` as a string using the `~s` ("write") formatter.
    pub fn format_write(&self, v: &ZuoValue) -> String {
        let res = unsafe { get_string(kernel_call(c"~s", &[v.as_raw()])) };
        String::from_utf8_lossy(res).into()
    }

    // == eval ==

    /// Evaluates the module given by `prog`, registering it under the given C-string `mod_name`.
    ///
    /// Note that evaluation may trigger garbage collection.
    pub fn eval_module(&self, mod_name: &CStr, prog: &str) -> ZuoValue {
        let res = unsafe {
            zuo_sys::zuo_ext_eval_module(
                symbol(mod_name),
                prog.as_ptr() as *const _,
                prog.len() as _,
            )
        };
        self.collect();
        self.stash(res)
    }

    /// Loads `mod_path` if it has not been loaded already and returns the hash table
    /// representation. See Zuo function `module->hash`.
    pub fn module_hash(&self, mod_name: &CStr) -> ZuoValue {
        let res = unsafe { kernel_call(c"module->hash", &[symbol(mod_name)]) };
        self.collect();
        self.stash(res)
    }

    /// Like `module_hash` but extracts an exported value. See Zuo function
    /// `dynamic-require`.
    pub fn dynamic_require(&self, mod_name: &CStr, sym: &CStr) -> ZuoValue {
        let res = unsafe {
            let mod_ht = kernel_call(c"module->hash", &[symbol(mod_name)]);
            let dynamic_require = hash_ref(mod_ht, symbol(c"dynamic-require"), None);
            apply(dynamic_require, &[symbol(mod_name), symbol(sym)])
        };
        self.collect();
        self.stash(res)
    }

    /// Reads all s-expressions from `prog`. See Zuo function `string-read`.
    pub fn read_all(&self, prog: &str) -> Vec<ZuoValue> {
        let vs = unsafe { ListIter::new(kernel_call(c"string-read", &[string(prog.as_bytes())])) };
        vs.map(|v| self.stash(v)).collect()
    }

    /// Reads the first s-expressions from `prog`. Returns `None` if none were read. See
    /// Zuo function `string-read`.
    pub fn read(&self, prog: &str) -> Option<ZuoValue> {
        let res = unsafe {
            let vs = kernel_call(c"string-read", &[string(prog.as_bytes())]);
            let null = zuo_sys::zuo_ext_null();
            if vs == null {
                None
            } else {
                Some(zuo_sys::zuo_ext_car(vs))
            }
        };
        res.map(|v| self.stash(v))
    }

    /// Evaluates the term as if it appeared in the `zuo/kernel` module. See Zuo function
    /// `kernel-eval`.
    pub fn kernel_eval(&self, term: &ZuoValue) -> ZuoValue {
        let res = unsafe { kernel_call(c"kernel-eval", &[term.as_raw()]) };
        self.collect();
        self.stash(res)
    }

    // == stash ==

    // Since values may get moved by garbage collection, we save all known `ZuoValues`
    // onto the "stash" stack (`zuo_ext_stash_{push,pop}`), and then save them in a
    // parallel stack in the `Zuo` struct. After doing anything which may have triggered a
    // collection, we pop everything off the stack in order to update any pointer which
    // may have been moved, then push them back onto the stack so that they will continue
    // to be saved. The stack stores weak pointers so that unreachable `ZuoValue`s are not
    // saved again.

    fn stash(&self, raw_v: *mut zuo_ext_t) -> ZuoValue {
        let mut stash = self.stash.borrow_mut();
        unsafe { zuo_sys::zuo_ext_stash_push(raw_v) };
        let v = ZuoValue::new(raw_v);
        stash.push(v.weak());
        v
    }

    fn collect(&self) {
        let mut stash = self.stash.borrow_mut();
        let mut temp = self.stash_temp.borrow_mut();

        debug_assert!(temp.is_empty());
        temp.clear();

        let mut pop = 0;
        let mut push = 0;

        while let Some(wr) = stash.pop() {
            pop += 1;
            let raw_v = unsafe { zuo_sys::zuo_ext_stash_pop() };
            if let Some(rc) = wr.upgrade() {
                if rc.get() != raw_v {
                    log::trace!("collect(): {:?} -> {:?}", rc.get(), raw_v);
                    rc.set(raw_v);
                }
                temp.push(rc);
                push += 1;
            }
        }

        while let Some(rc) = temp.pop() {
            let raw_v = rc.get();
            unsafe { zuo_sys::zuo_ext_stash_push(raw_v) };
            stash.push(Rc::downgrade(&rc));
        }

        stash.shrink_to_fit();
        temp.shrink_to_fit();

        if pop != push {
            log::debug!("collect(): done -{pop} +{push}");
        }
    }
}

impl fmt::Debug for Zuo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Zuo").finish_non_exhaustive()
    }
}

// == builder ==

#[derive(Default)]
pub struct ZuoBuilder {
    lib_path: Option<PathBuf>,
}

static ZUO_DID_INIT: atomic::AtomicBool = atomic::AtomicBool::new(false);

impl ZuoBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    /// Initialize Zuo, returning a handle to the interpeter. This may only be called one
    /// time in the lifetime of a program, in order to prevent clashing global state.
    pub fn init(&self) -> Option<Zuo> {
        if ZUO_DID_INIT.swap(true, atomic::Ordering::Relaxed) {
            return None;
        }

        Some(unsafe { self.init_unchecked() })
    }

    /// Initialize Zuo, returning a handle to the interpeter. This does not count for the
    /// single initialization check from [`ZuoBuilder::init`].
    ///
    /// # Safety
    ///
    /// - It is undefined behavior to use two [`Zuo`] instances simultaneously, since they
    ///   use overlapping global state.
    pub unsafe fn init_unchecked(&self) -> Zuo {
        Zuo::do_init(self.lib_path.as_deref())
    }

    /// Specify the module load path for Zuo. By default, there will be no load path, so
    /// Zuo will be unable to load modules from the filesystem.
    pub fn lib_path(&mut self, path: impl Into<PathBuf>) -> &mut Self {
        self.lib_path = Some(path.into());
        self
    }
}

// == Raw value operations ==

unsafe fn is_not_false(v: *mut zuo_ext_t) -> bool {
    v != zuo_sys::zuo_ext_false()
}

unsafe fn string(bs: &[u8]) -> *mut zuo_ext_t {
    zuo_sys::zuo_ext_string(bs.as_ptr() as *const _, bs.len() as _)
}

unsafe fn get_string(v: *mut zuo_ext_t) -> &'static [u8] {
    std::slice::from_raw_parts(
        zuo_sys::zuo_ext_string_ptr(v) as *const u8,
        zuo_sys::zuo_ext_string_length(v) as usize,
    )
}

unsafe fn hash_ref(
    ht: *mut zuo_ext_t,
    key: *mut zuo_ext_t,
    dflt: Option<*mut zuo_ext_t>,
) -> *mut zuo_ext_t {
    let dflt = dflt.unwrap_or_else(|| zuo_sys::zuo_ext_false());
    zuo_sys::zuo_ext_hash_ref(ht, key, dflt)
}

unsafe fn symbol(s: &CStr) -> *mut zuo_ext_t {
    zuo_sys::zuo_ext_symbol(s.as_ptr())
}

unsafe fn list(vs: &[*mut zuo_ext_t]) -> *mut zuo_ext_t {
    let mut tl = zuo_sys::zuo_ext_null();
    for &v in vs.iter().rev() {
        tl = zuo_sys::zuo_ext_cons(v, tl);
    }
    tl
}

unsafe fn apply(proc: *mut zuo_ext_t, args: &[*mut zuo_ext_t]) -> *mut zuo_ext_t {
    zuo_sys::zuo_ext_apply(proc, list(args))
}

unsafe fn kernel_call(proc: &CStr, args: &[*mut zuo_ext_t]) -> *mut zuo_ext_t {
    log::trace!("kernel_call: {proc:?}");
    let env = zuo_sys::zuo_ext_kernel_env();
    apply(hash_ref(env, symbol(proc), None), args)
}

struct ListIter {
    list: *mut zuo_ext_t,
    len: usize,
}

impl ListIter {
    unsafe fn new(list: *mut zuo_ext_t) -> Self {
        let len = kernel_call(c"length", &[list]);
        let len = zuo_sys::zuo_ext_integer_value(len) as usize;
        Self { list, len }
    }
}

impl Iterator for ListIter {
    type Item = *mut zuo_ext_t;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            let (car, cdr) = unsafe {
                (
                    zuo_sys::zuo_ext_car(self.list),
                    zuo_sys::zuo_ext_cdr(self.list),
                )
            };
            self.list = cdr;
            self.len -= 1;
            Some(car)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

// == Safe value wrapper ==

/// Safe wrapper around a Zuo value. These are refcounted handles to the underlying value
/// pointers, which automatically prevents them from being garbage collected. You can
/// freely clone a [`ZuoValue`] since it is refcounted.
#[derive(Clone)]
#[repr(transparent)]
pub struct ZuoValue {
    rc: Root,
}

type Root = Rc<Cell<*mut zuo_ext_t>>;
type WeakRoot = Weak<Cell<*mut zuo_ext_t>>;

impl ZuoValue {
    fn new(raw_v: *mut zuo_ext_t) -> Self {
        Self {
            rc: Rc::new(Cell::new(raw_v)),
        }
    }

    fn weak(&self) -> WeakRoot {
        Rc::downgrade(&self.rc)
    }

    /// Get the underlying pointer for this value. This pointer may become invalid if
    /// garbage collection is triggered.
    pub fn as_raw(&self) -> *mut zuo_ext_t {
        self.rc.get()
    }
}

/// Checks that the underlying pointers are the same.
impl PartialEq for ZuoValue {
    fn eq(&self, other: &ZuoValue) -> bool {
        self.as_raw() == other.as_raw()
    }
}

/// Checks that the underlying pointers are the same.
impl PartialEq<*mut zuo_ext_t> for ZuoValue {
    fn eq(&self, other: &*mut zuo_ext_t) -> bool {
        self.as_raw() == *other
    }
}

/// Checks that the underlying pointers are the same.
impl Eq for ZuoValue {}
