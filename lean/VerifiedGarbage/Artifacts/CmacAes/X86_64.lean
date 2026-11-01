module

public import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CMAC's chaining with AES-NI on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.X86_64

def artifacts : List Artifact := [
  ]

end VG.Artifacts.CmacAes.X86_64
