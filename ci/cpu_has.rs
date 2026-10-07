//! Prints the CPU features of a `VG_CPU_FEATURES` value (its only argument)
//! that this machine lacks, separated by spaces, for the Benchmarks workflow:
//! `VG_CPU_FEATURES` only removes features, so a configuration naming one the
//! runner lacks measures another configuration's implementations, not its
//! own (`.github/workflows/bench.yml` skips it).
//!
//!     rustc -O -o cpu_has ci/cpu_has.rs && ./cpu_has avx,avx2,avx512f
//!
//! The names are `src/cpu.rs`'s `NAMES`, Rust's `target_feature` names,
//! which std's detection macros take too; like `src/cpu.rs`, they also ask
//! whether the operating system has enabled the registers a feature needs.
//! An empty value or `none` names nothing. A name not listed here for this
//! architecture exits with status 2 (`ci/test_check_benchmarks.py` checks
//! that every name `src/cpu.rs` detects on an architecture is listed).

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn has(name: &str) -> Option<bool> {
    Some(match name {
        "ssse3" => is_x86_feature_detected!("ssse3"),
        "sha" => is_x86_feature_detected!("sha"),
        "aes" => is_x86_feature_detected!("aes"),
        "pclmulqdq" => is_x86_feature_detected!("pclmulqdq"),
        "avx" => is_x86_feature_detected!("avx"),
        "avx2" => is_x86_feature_detected!("avx2"),
        "bmi1" => is_x86_feature_detected!("bmi1"),
        "bmi2" => is_x86_feature_detected!("bmi2"),
        "avx512f" => is_x86_feature_detected!("avx512f"),
        "sha512" => is_x86_feature_detected!("sha512"),
        "adx" => is_x86_feature_detected!("adx"),
        "avx512ifma" => is_x86_feature_detected!("avx512ifma"),
        "avx512vl" => is_x86_feature_detected!("avx512vl"),
        "vaes" => is_x86_feature_detected!("vaes"),
        "vpclmulqdq" => is_x86_feature_detected!("vpclmulqdq"),
        "avx512bw" => is_x86_feature_detected!("avx512bw"),
        _ => return None,
    })
}

#[cfg(target_arch = "aarch64")]
fn has(name: &str) -> Option<bool> {
    Some(match name {
        "neon" => std::arch::is_aarch64_feature_detected!("neon"),
        "aes" => std::arch::is_aarch64_feature_detected!("aes"),
        "sha2" => std::arch::is_aarch64_feature_detected!("sha2"),
        "sha3" => std::arch::is_aarch64_feature_detected!("sha3"),
        "sve2" => std::arch::is_aarch64_feature_detected!("sve2"),
        _ => return None,
    })
}

/// No features are detected on the other architectures (`src/cpu.rs`).
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
fn has(_: &str) -> Option<bool> {
    None
}

fn main() {
    let value = std::env::args().nth(1).unwrap_or_default();
    if value.is_empty() || value == "none" {
        return;
    }
    let mut missing = Vec::new();
    for name in value.split(',') {
        match has(name) {
            Some(true) => {}
            Some(false) => missing.push(name),
            None => {
                eprintln!("cpu_has: {name:?} is not a feature this architecture detects");
                std::process::exit(2);
            }
        }
    }
    println!("{}", missing.join(" "));
}
