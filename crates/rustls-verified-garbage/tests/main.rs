//! Every test of the provider outside its own unit tests, in one binary:
//! a binary each, they compiled and linked rustls and the library's code
//! five times over.

mod hash;
mod hkdf;
mod kx;
mod provider;
mod records;
