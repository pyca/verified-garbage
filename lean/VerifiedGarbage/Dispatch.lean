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

/-- The implementations of AES-GCM on x86-64, by suffix, best first. -/
def gcmX86_64 : List String := ["_vaes_vpclmul_avx512", "_vaes_vpclmul", "_vaes_pclmul",
  "_aesni_vpclmul", "_aesni_pclmul_avx", "_aesni_pclmul", "_vaes", "_aesni", "_vpclmul", "_pclmul"]

def ranking : Rust.Ranking := [
  ("x86_64",
    -- AES-SIV's CMAC by AES-NI's CBC code, which it runs on long inputs.
    { suffix := "_aesni_cbc", skip := true } ::
    -- AES-GCM-SIV: each of AES-GCM's implementations with its AVX2 copies
    -- (`_avx2`), then without.
    ((gcmX86_64 ++ [""]).flatMap fun g =>
      [{ suffix := g ++ "_avx2", modules := ["aes_gcm_siv"] }] ++
        if g.isEmpty then [] else [{ suffix := g, modules := ["aes_gcm_siv"] }]) ++
    { suffix := "_vaes_avx512" } ::
    gcmX86_64.map (fun g => { suffix := g }) ++ [
    -- ChaCha20's 512-bit code (`_avx512`) is chosen where ChaCha20-Poly1305's
    -- `_ifma` is, on CPUs with AVX512_IFMA, and `_avx512vl` on the other CPUs
    -- with AVX512VL.
    { suffix := "_avx512", modules := ["chacha20"], extra := ["avx512ifma"] },
    { suffix := "_ifma" },
    { suffix := "_avx512vl" },
    -- ML-DSA's `_avx512` key preparation is its `_avx2` code but for the name
    -- of the NTT it calls (whose two instances are the same code), needing
    -- only AVX2: it is chosen where its other `_avx512` functions are, and
    -- `_avx2` on the other CPUs.
    { suffix := "_avx512", modules := ["mldsa44", "mldsa65", "mldsa87"],
      extra := ["avx512f", "avx512vl"] },
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
    -- AES-SIV's CMAC by the AES extension's CBC code, which it runs on long inputs.
    { suffix := "_aes_cbc", skip := true },
    { suffix := "_aes_sha3" },
    { suffix := "_aes" },
    -- FEAT_SHA3's Keccak is faster on Apple's cores, and slower on Neoverse N2:
    -- ML-KEM's, SHA-3's and Ed448's. Elsewhere `_sha3` is SHA-512's code, or
    -- ML-DSA's, which is chosen on every CPU with FEAT_SHA3.
    { suffix := "_x2_sha3_keccak_sha3", vendor := some "apple" },
    { suffix := "_x2_sha3" },
    { suffix := "_sha3", modules := ["sha3", "ed448"], vendor := some "apple" },
    { suffix := "_sha3" },
    { suffix := "_sha2" },
    { suffix := "_sve2" },
    -- Poly1305's NEON code is faster on Apple's cores (about twice as fast),
    -- and slower on Neoverse N2. It needs no feature (AdvSIMD is part of the
    -- AArch64 baseline): `neon`, which detection reports, lets
    -- `VG_CPU_FEATURES=neon` choose it elsewhere for the tests.
    { suffix := "_neon", modules := ["poly1305"], extra := ["neon"], vendor := some "apple" },
    { suffix := "_neon" }]),
  ("arm", [
    { suffix := "_umaal" }])]

end VG.Dispatch
