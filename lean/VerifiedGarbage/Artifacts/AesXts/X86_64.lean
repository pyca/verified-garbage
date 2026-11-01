module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Verified
public import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64: none of its own (its whole-block functions are internal) -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86_64


def artifacts : List Artifact := [
  ]

end VG.Artifacts.AesXts.X86_64
