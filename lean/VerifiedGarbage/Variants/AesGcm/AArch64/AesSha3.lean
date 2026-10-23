module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-!
# The functions AES-GCM calls on AArch64: AesSha3

A variant of `AesGcm` on AArch64 (see `TCB/Emit.lean`): `Aes`'s, with `seal`
and `open` taking the records of TLS with the loops that interleave counter
mode and GHASH eight blocks at a time (`GcmImpl.stitch`), which also need
`FEAT_SHA3` (Rust's `sha3` feature) for `eor3`.
-/

@[expose] public section

namespace VG.Variants.AesGcm.AArch64.AesSha3

def variant : Proof.AesGcm.AArch64.GcmVariant := ⟨.aese, .aese, .aes, true, true⟩

end VG.Variants.AesGcm.AArch64.AesSha3
