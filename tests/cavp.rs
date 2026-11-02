//! The NIST CAVP tests (`cavp/main.rs`), in a test binary of their own: the
//! largest directory of tests, so that it compiles in parallel with every
//! other directory's, in `tests/main.rs`. Its tests keep their paths there
//! (`cavp::…`), and it declares the shared modules it uses, as
//! `tests/main.rs` does.

// Some of its functions only the tests of `tests/main.rs` use.
#[allow(dead_code)]
mod bytes;
#[allow(dead_code)]
mod modes;
mod vectors;

#[path = "cavp/main.rs"]
mod cavp;
