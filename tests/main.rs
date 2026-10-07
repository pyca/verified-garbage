//! Every test outside the library's own unit tests, in one binary: each
//! directory here is a module, `#[path]`-declared below, whose `main.rs`
//! documents what it tests. One binary runs all of them on one pool of
//! threads, and starts once, rather than once per directory, in every
//! `cargo test` (a second or more each under Intel SDE). `autotests = false`
//! (Cargo.toml) keeps Cargo from building each directory as a binary of its
//! own as well, so a directory that is not listed here does not run:
//! `ci/check_arch_gates.py` checks that every one is.

#[path = "acvp/main.rs"]
mod acvp;
#[path = "blake2_kat/main.rs"]
mod blake2_kat;
#[path = "cavp/main.rs"]
mod cavp;
#[path = "pbkdf2/main.rs"]
mod pbkdf2;
#[path = "rfc1321/main.rs"]
mod rfc1321;
#[path = "rfc2202/main.rs"]
mod rfc2202;
#[path = "rfc6229/main.rs"]
mod rfc6229;
#[path = "rfc6979/main.rs"]
mod rfc6979;
#[path = "rfc7253/main.rs"]
mod rfc7253;
#[path = "rfc7693/main.rs"]
mod rfc7693;
#[path = "rfc7748/main.rs"]
mod rfc7748;
#[path = "rfc7914/main.rs"]
mod rfc7914;
#[path = "rfc8032/main.rs"]
mod rfc8032;
#[path = "rfc8439/main.rs"]
mod rfc8439;
#[path = "rfc9106/main.rs"]
mod rfc9106;
#[path = "rsa_guidance/main.rs"]
mod rsa_guidance;
#[path = "wycheproof/main.rs"]
mod wycheproof;
