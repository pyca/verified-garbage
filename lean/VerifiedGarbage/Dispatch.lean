module

public import VerifiedGarbage.TCB.Rust

/-! # The ranking of the dispatchers

Each target's order of the implementations its dispatchers try
(`VG.Rust.Rank`), best first. It decides only which implementation runs on a
CPU that could run several, so it is a matter of speed, not of correctness
or safety, and is not trusted: whatever it says, a dispatcher calls only
implementations proven against its documented contract, each only where
the CPU has the features it needs. An implementation whose suffix is not
here, or not made of parts that are (`VG.Rust.partsOf`), fails the emitter.
-/

@[expose] public section

namespace VG.Dispatch

open VG.Rust (Rank)

def ranking : Rust.Ranking := [
  ("x86_64", [
    { suffix := "_vaes_avx512" },
    -- Each implementation with AVX2 copies (`_avx2`, AES-GCM-SIV's) before
    -- the same one without.
    { suffix := "_vaes_vpclmul_avx512" },
    { suffix := "_vaes_vpclmul" },
    { suffix := "_vaes_pclmul_avx2" },
    { suffix := "_vaes_pclmul" },
    { suffix := "_aesni_vpclmul_avx2" },
    { suffix := "_aesni_vpclmul" },
    { suffix := "_aesni_pclmul_avx_avx2" },
    { suffix := "_aesni_pclmul_avx" },
    { suffix := "_aesni_pclmul" },
    { suffix := "_vaes_avx2" },
    { suffix := "_vaes" },
    { suffix := "_aesni_avx2" },
    -- AES-NI code that also wipes its scratch with `vg_zeroize_avx`.
    { suffix := "_aesni_avx" },
    { suffix := "_aesni" },
    { suffix := "_vpclmul_avx2" },
    { suffix := "_vpclmul" },
    -- `vg_aes_gcm_prepare`'s 128-bit AVX code, after its 256-bit code.
    { suffix := "_pclmul_avx" },
    { suffix := "_pclmul_avx2" },
    { suffix := "_pclmul" },
    { suffix := "_ifma" },
    { suffix := "_avx512vl" },
    { suffix := "_avx512" },
    { suffix := "_shani" },
    { suffix := "_avx_bmi" },
    { suffix := "_avx2" },
    { suffix := "_adx" },
    { suffix := "_avx" },
    { suffix := "_ssse3" }]),
  ("x86", [
    { suffix := "_aesni_pclmul" },
    { suffix := "_aesni" },
    { suffix := "_pclmul" },
    { suffix := "_shani" },
    { suffix := "_ssse3" }]),
  ("aarch64", [
    { suffix := "_aes_sha3" },
    { suffix := "_aes" },
    { suffix := "_x2_sha3_keccak_sha3" },
    { suffix := "_x2_sha3" },
    { suffix := "_sha3" },
    { suffix := "_sha512" },
    { suffix := "_sha2" },
    { suffix := "_sve2" },
    { suffix := "_neon" }]),
  ("arm", [
    { suffix := "_umaal" }])]

end VG.Dispatch
