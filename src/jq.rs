//! This module takes the unsafe bindings from `jq-sys` then (hopefully)
//! wrapping to present a slightly safer API to use.
//!
//! These are building blocks and not intended for use from the public API.

use crate::errors::{Error, Result};
use jq_sys::{
    jq_compile, jq_format_error, jq_get_exit_code, jq_halted, jq_init, jq_next, jq_set_error_cb,
    jq_start, jq_state, jq_teardown, jv, jv_array, jv_array_append, jv_copy, jv_dump_string,
    jv_free, jv_get_kind, jv_invalid_get_msg, jv_invalid_has_msg, jv_kind_JV_KIND_INVALID,
    jv_kind_JV_KIND_NUMBER, jv_kind_JV_KIND_STRING, jv_number_value, jv_parser, jv_parser_free,
    jv_parser_new, jv_parser_next, jv_parser_remaining, jv_parser_set_buf, jv_string_value,
};
use std::ffi::{CStr, CString};
use std::iter;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::os::raw::{c_char, c_void};

use itertools::{Itertools as _, Position};

pub struct Jq {
    state: *mut jq_state,
    err_buf: String,
}

/// A type that can be resolved into an iterator of JSON values,
/// which could serve as the inputs to a JQ program.
pub trait IntoJv<'a> {
    /// Instantiates a new iterator of JSON objects.
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> + 'a;
}

impl IntoJv<'static> for Vec<Jv> {
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> {
        self.into_iter().map(Ok)
    }
}

impl<'a> IntoJv<'a> for &'a [Jv] {
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> + 'a {
        self.iter().cloned().map(Ok)
    }
}

impl<'a> IntoJv<'a> for &'a CStr {
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> + 'a {
        self.to_bytes().into_jv()
    }
}

impl<'a> IntoJv<'a> for &'a str {
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> + 'a {
        self.as_bytes().into_jv()
    }
}

impl<'a> IntoJv<'a> for &'a [u8] {
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> + 'a {
        Chunks([self]).into_jv()
    }
}

/// An adaptor for [`IntoJv`] for discontinuous chunks of bytes.
pub struct Chunks<I>(pub I);

impl<'a, I: IntoIterator<Item = &'a [u8]> + 'a> IntoJv<'a> for Chunks<I> {
    fn into_jv(self) -> impl Iterator<Item = Result<Jv>> + 'a {
        let parser = Parser::new();
        parser.parse_multi(self.0.into_iter())
    }
}

impl Jq {
    pub fn compile_program(program: CString) -> Result<Self> {
        let mut jq = Jq {
            state: {
                // jq's master branch shows this can be a null pointer, in
                // which case the binary will exit with a `Error::System`.
                let ptr = unsafe { jq_init() };
                if ptr.is_null() {
                    return Err(Error::System {
                        reason: Some("Failed to init".into()),
                    });
                } else {
                    ptr
                }
            },
            err_buf: "".to_string(),
        };

        extern "C" fn err_cb(data: *mut c_void, msg: jv) {
            unsafe {
                let formatted = jq_format_error(msg);
                let jq = &mut *(data as *mut Jq);
                jq.err_buf += &(CStr::from_ptr(jv_string_value(formatted))
                    .to_str()
                    .unwrap_or("")
                    .to_string()
                    + "\n");
                jv_free(formatted);
            }
        }
        unsafe {
            jq_set_error_cb(jq.state, Some(err_cb), &mut jq as *mut Jq as *mut c_void);
        }

        if unsafe { jq_compile(jq.state, program.as_ptr()) } == 0 {
            Err(Error::InvalidProgram {
                reason: jq.err_buf.clone(),
            })
        } else {
            Ok(jq)
        }
    }

    fn is_halted(&self) -> bool {
        unsafe { jq_halted(self.state) != 0 }
    }

    fn get_exit_code(&self) -> ExitCode {
        let exit_code = Jv {
            ptr: unsafe { jq_get_exit_code(self.state) },
        };

        // The rules for this seem odd, but I'm trying to model this after the
        // similar block in the jq `main.c`s `process()` function.

        if exit_code.is_valid() {
            ExitCode::JQ_OK
        } else {
            exit_code
                .as_number()
                .map(|i| (i as isize).into())
                .unwrap_or(ExitCode::JQ_ERROR_UNKNOWN)
        }
    }

    /// Run the jq program against the first value in the input.
    pub fn execute<'a>(
        &mut self,
        input: impl IntoJv<'a>,
        mut output_sink: impl FnMut(Jv),
    ) -> Result<()> {
        let Some(initial_value) = input.into_jv().next() else {
            return Ok(()); // no input, so no output
        };
        let initial_value = initial_value?;

        unsafe {
            // `jq_start` seems to be a consuming call.
            // In order to avoid a double-free, when `initial_value` is dropped,
            // we have to use `jv_copy` on the inner `jv`.
            jq_start(self.state, jv_copy(initial_value.ptr), 0);
            // After, we can manually free the `initial_value` with `drop` since
            // it is no longer needed.
            drop(initial_value);

            while let Some(result) = self.next_result() {
                let result = result?;

                output_sink(result);
            }
        }

        Ok(())
    }

    /// Run the jq program against an iterator of inputs that would get slurped.
    pub fn execute_slurped<'a>(
        &mut self,
        input: impl IntoJv<'a>,
        output_sink: impl FnMut(Jv),
    ) -> Result<()> {
        let mut slurped = Jv {
            ptr: unsafe { jv_array() },
        };

        for item in input.into_jv() {
            slurped.ptr = unsafe { jv_array_append(slurped.ptr, item?.into_raw()) };
        }

        self.execute(vec![slurped], output_sink)
    }

    fn next_result(&mut self) -> Option<Result<Jv>> {
        let value = Jv {
            ptr: unsafe { jq_next(self.state) },
        };
        if value.is_valid() {
            Some(Ok(value))
        } else {
            if let Err(err) = unsafe { report_jq_err(self, &value) } {
                return Some(Err(err));
            }

            value.get_msg().map(|reason| {
                Err(Error::System {
                    reason: Some(reason),
                })
            })
        }
    }
}

impl Drop for Jq {
    fn drop(&mut self) {
        unsafe { jq_teardown(&mut self.state) }
    }
}

/// A handle to a JSON value that can be passed into a JQ program or rendered as a string.
pub struct Jv {
    ptr: jv,
}

impl Jv {
    /// Convert the current `JV` into the "dump string" rendering of itself.
    pub fn as_dump_string(&self) -> Result<String> {
        let dump = Jv {
            ptr: unsafe { jv_dump_string(jv_copy(self.ptr), 0) },
        };
        unsafe { get_string_value(jv_string_value(dump.ptr)) }
    }

    /// Attempts to extract feedback from jq if the JV is invalid.
    pub fn get_msg(&self) -> Option<String> {
        if self.invalid_has_msg() {
            let reason = {
                let msg = Jv {
                    ptr: unsafe {
                        // This call is gross since we're dipping outside of the
                        // safe/drop-enabled wrapper to get a copy which will be freed
                        // by jq. If we wrap it in a `JV`, we'll run into a double-free
                        // situation.
                        jv_invalid_get_msg(jv_copy(self.ptr))
                    },
                };

                format!(
                    "JQ: Parse error: {}",
                    msg.as_string().unwrap_or_else(|_| "unknown".into())
                )
            };
            Some(reason)
        } else {
            None
        }
    }

    /// Returns the underlying number if the value is a number.
    pub fn as_number(&self) -> Option<f64> {
        unsafe {
            if jv_get_kind(self.ptr) == jv_kind_JV_KIND_NUMBER {
                Some(jv_number_value(self.ptr))
            } else {
                None
            }
        }
    }

    /// Returns the underlying string if the value is a number.
    pub fn as_string(&self) -> Result<String> {
        unsafe {
            if jv_get_kind(self.ptr) == jv_kind_JV_KIND_STRING {
                get_string_value(jv_string_value(self.ptr))
            } else {
                Err(Error::Unknown)
            }
        }
    }

    /// Returns whether the value is a valid, serializable value.
    pub fn is_valid(&self) -> bool {
        unsafe { jv_get_kind(self.ptr) != jv_kind_JV_KIND_INVALID }
    }

    fn invalid_has_msg(&self) -> bool {
        unsafe { jv_invalid_has_msg(jv_copy(self.ptr)) == 1 }
    }

    pub(crate) fn into_raw(self) -> jv {
        let this = ManuallyDrop::new(self);
        this.ptr
    }
}

impl Clone for Jv {
    fn clone(&self) -> Self {
        Jv {
            ptr: unsafe { jv_copy(self.ptr) },
        }
    }
}

impl Drop for Jv {
    fn drop(&mut self) {
        unsafe { jv_free(self.ptr) };
    }
}

struct Parser {
    ptr: *mut jv_parser,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            ptr: unsafe { jv_parser_new(0) },
        }
    }

    pub fn parse_multi<'a>(
        self,
        inputs: impl Iterator<Item = &'a [u8]> + 'a,
    ) -> impl Iterator<Item = Result<Jv>> + 'a {
        let jq = self.ptr;

        inputs
            .with_position()
            .flat_map(move |(pos, input)| {
                unsafe {
                    let is_partial = match pos {
                        Position::First | Position::Middle => 1,
                        Position::Only | Position::Last => 0,
                    };
                    jv_parser_set_buf(
                        jq,
                        input.as_ptr().cast::<i8>(),
                        input.len() as i32,
                        is_partial,
                    );
                }

                iter::repeat(())
                    .take_while(move |()| unsafe { jv_parser_remaining(jq) } != 0)
                    .filter_map(move |()| {
                        let value = Jv {
                            ptr: unsafe { jv_parser_next(jq) },
                        };

                        if value.is_valid() {
                            Some(Ok(value))
                        } else if unsafe { jv_invalid_has_msg(jv_copy(value.ptr)) } != 0 {
                            Some(Err(Error::System {
                                reason: Some(
                                    value
                                        .get_msg()
                                        .unwrap_or_else(|| "JQ: Parser error".to_string()),
                                ),
                            }))
                        } else {
                            None
                        }
                    })
            })
            .take_while_inclusive(|result| result.is_ok()) // fuse the iterator when an error is encountered to avoid working on invalid objects
            .chain(empty_iter_with_finalizer(move || {
                drop(self);
            }))
    }
}

fn empty_iter_with_finalizer<T, F: FnOnce()>(f: F) -> impl iter::FusedIterator<Item = T> {
    struct Iter<T, F>(Option<F>, PhantomData<T>);

    impl<T, F: FnOnce()> Iterator for Iter<T, F> {
        type Item = T;

        fn next(&mut self) -> Option<Self::Item> {
            if let Some(f) = self.0.take() {
                f();
            }

            None
        }
    }

    impl<T, F: FnOnce()> iter::FusedIterator for Iter<T, F> {}

    Iter(Some(f), PhantomData)
}

impl Drop for Parser {
    fn drop(&mut self) {
        unsafe {
            jv_parser_free(self.ptr);
        }
    }
}

/// Takes a pointer to a nul term string, and attempts to convert it to a String.
unsafe fn get_string_value(value: *const c_char) -> Result<String> {
    let s = CStr::from_ptr(value).to_str()?;
    Ok(s.to_owned())
}

unsafe fn report_jq_err(jq: &Jq, value: &Jv) -> Result<()> {
    if jq.is_halted() {
        use ExitCode::*;
        match jq.get_exit_code() {
            JQ_ERROR_SYSTEM => Err(Error::System {
                reason: value.get_msg(),
            }),
            // As far as I know, we should not be able to see a compile error
            // this deep into the execution of a jq program (it would need to be
            // compiled already, right?)
            // Still, compile failure is represented by an exit code, so in
            // order to be exhaustive we have to check for it.
            JQ_ERROR_COMPILE => Err(Error::InvalidProgram {
                reason: jq.err_buf.clone(),
            }),
            // Any of these `OK_` variants are "success" cases.
            // I suppose the jq program can halt successfully, or not, or not at
            // all and still terminate some other way?
            JQ_OK | JQ_OK_NULL_KIND | JQ_OK_NO_OUTPUT => Ok(()),
            JQ_ERROR_UNKNOWN => Err(Error::Unknown),
        }
    } else {
        Ok(())
    }
}

/// Various exit codes jq checks for during the `if (jq_halted(jq))` branch of
/// their processing loop.
///
/// Adapted from the enum seen in jq's master branch right now.
/// The numbers seem to line up with the magic numbers seen in
/// the 1.6 release, though there's no enum that I saw at that point in the git
/// history.
#[allow(non_camel_case_types, dead_code)]
#[rustfmt::skip]
enum ExitCode {
    JQ_OK               =  0,
    JQ_OK_NULL_KIND     = -1,
    JQ_ERROR_SYSTEM     =  2,
    JQ_ERROR_COMPILE    =  3,
    JQ_OK_NO_OUTPUT     = -4,
    JQ_ERROR_UNKNOWN    =  5,
}

impl From<isize> for ExitCode {
    #[rustfmt::skip]
    fn from(number: isize) -> Self {
        use ExitCode::*;
        match number {
             0 => JQ_OK,
            -1 => JQ_OK_NULL_KIND,
             2 => JQ_ERROR_SYSTEM,
             3 => JQ_ERROR_COMPILE,
            -4 => JQ_OK_NO_OUTPUT,
             // `5` is called out explicitly in the jq source, but also "unknown"
             // seems to make good sense for other unexpected number.
             5 | _ => JQ_ERROR_UNKNOWN,
        }
    }
}
