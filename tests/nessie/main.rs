//! NESSIE known-answer tests, as pyca/cryptography reformatted them
//! (<https://www.cosic.esat.kuleuven.be/nessie/testvectors/>), vendored
//! under `vectors/` (see `vectors/sources/` for where each file comes from)
//! and compiled into the test binary, so these tests always run. Every
//! vector of every file is checked.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

mod idea_ecb;
