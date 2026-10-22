module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee

/-!
# The variants of SM4-GCM on AArch64

What a variant of `Sm4Gcm` on AArch64 is (`Variants/Sm4Gcm/AArch64/`): the
implementation of `vg_ghash` its functions call, by name (`GhashName`), as
AES-GCM's. The implementations themselves (`GcmVariant.impl`) are in
`Impls.lean`, which only the generic file imports: their proofs import the
algebra of `Proof/Gcm/Poly.lean`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

/-- A variant of `Sm4Gcm` on AArch64: the implementation of `vg_ghash` it calls. -/
structure GcmVariant where
  gh : AesGcm.AArch64.GhashName

end VG.Proof.Sm4Gcm.AArch64
