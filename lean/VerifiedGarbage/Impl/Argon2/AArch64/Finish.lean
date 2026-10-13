module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Impl.Argon2.AArch64.FinalReduction
public import VerifiedGarbage.Impl.Argon2.AArch64.FinalOutput

/-! The complete final reduction and H′, parameterized by the hash backend. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.Finish

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq FinalReduction.code (FinalOutput.code name h)

end VG.Impl.Argon2.AArch64.Finish
