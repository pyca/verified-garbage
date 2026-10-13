module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
public import VerifiedGarbage.Impl.Argon2.AArch64.Finish

/-! Complete all filling passes, reduce the lane endings, and compute the final tag. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.FillFinish

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq FillIterations.loop (Finish.code name h)

end VG.Impl.Argon2.AArch64.FillFinish
