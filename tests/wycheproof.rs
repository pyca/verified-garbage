//! The Wycheproof tests (`wycheproof/main.rs`), in a test binary of their own,
//! as CAVP's are (`tests/cavp.rs`): nearly half of the code of
//! `tests/main.rs`, whose type checking is one thread's work, so that the two
//! compile in parallel. Its tests keep their paths there (`wycheproof::…`),
//! and it declares the shared modules it uses, as `tests/main.rs` does.

// Some of their functions only the tests of `tests/main.rs` use.
#[allow(dead_code)]
mod bytes;
#[allow(dead_code)]
mod json;

#[path = "wycheproof/main.rs"]
mod wycheproof;
