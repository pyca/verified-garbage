module

public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on x86 -/

@[expose] public section

namespace VG.Artifacts.Gcm.X86

def artifacts : List Artifact := [
  ]

end VG.Artifacts.Gcm.X86
