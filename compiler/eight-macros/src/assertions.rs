//! Assertion macros
//!
//! This module contains macros for performing assertions. Notable macros defined in this module
//! are:
//!
//! - [`assert_ok!`]
//! - [`assert_err!`]
//! - [`assert_some!`]
//! - [`assert_none!`]
//!
//! This module is only available when the `assertion-macros` feature is enabled.

/// Assert that a `Result` is `Ok`, returning the value inside the `Ok` variant.
#[macro_export]
macro_rules! assert_ok {
    ($expr:expr) => {{
        match $expr {
            ::std::result::Result::Ok(val) => val,
            ::std::result::Result::Err(err) => {
                panic!("assertion failed: Err({:?})", err);
            }
        }
    }};
}

/// Assert that a `Result` is `Err`, returning the error inside the `Err` variant.
#[macro_export]
macro_rules! assert_err {
    ($expr:expr) => {{
        match $expr {
            ::std::result::Result::Ok(val) => {
                panic!("assertion failed: Ok({:?})", val);
            }
            ::std::result::Result::Err(err) => err,
        }
    }};
}

/// Assert that an `Option` is `Some`, returning the value inside the `Some` variant.
#[macro_export]
macro_rules! assert_some {
    ($expr:expr) => {{
        match $expr {
            ::std::option::Option::Some(val) => val,
            ::std::option::Option::None => {
                panic!("assertion failed: None");
            }
        }
    }};
}

/// Assert that an `Option` is `None`.
#[macro_export]
macro_rules! assert_none {
    ($expr:expr) => {{
        if let ::std::option::Option::Some(val) = $expr {
            panic!("assertion failed: Some({:?})", val);
        };
    }};
}

#[macro_export]
macro_rules! assert_matches {
    ($expr:expr, $ty:pat_param => $output:expr) => {{
        match $expr {
            $ty => $output,
            _ => {
                assert!(
                    false,
                    "assertion failed: expected {:?} to match {:?}",
                    $expr,
                    stringify!($ty)
                );
                unreachable!();
            }
        }
    }};
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_std_result_assertions() {
        let result: Result<i32, &str> = Ok(42);
        assert_eq!(assert_ok!(result), 42);
        let result: Result<i32, &str> = Err("error");
        assert_eq!(assert_err!(result), "error");
    }

    #[test]
    fn test_std_option_assertions() {
        let option: Option<i32> = Some(42);
        assert_eq!(assert_some!(option), 42);
        let option: Option<i32> = None;
        assert_none!(option);
    }

    #[test]
    #[should_panic]
    fn test_assert_ok_err() {
        let result: Result<i32, &str> = Err("error");
        assert_ok!(result);
        let result: Result<i32, &str> = Ok(42);
        assert_err!(result);
    }

    #[test]
    #[should_panic]
    fn test_assert_some_none() {
        let option: Option<i32> = None;
        assert_some!(option);
        let option: Option<i32> = Some(42);
        assert_none!(option);
    }
}
