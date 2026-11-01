module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on AArch64: none of its own (its whole-block functions are internal) -/

@[expose] public section

namespace VG.Artifacts.AesXts.AArch64

open VG.Proof.AesXts.AArch64

def artifacts : List Artifact := [
  ]

end VG.Artifacts.AesXts.AArch64
