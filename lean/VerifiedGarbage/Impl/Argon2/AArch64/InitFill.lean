module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
public import VerifiedGarbage.Impl.Argon2.AArch64.FillSetup
public import VerifiedGarbage.Impl.Argon2.AArch64.FillFinish

/-! All memory initialization, filling and finalization after H₀ has been computed. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.InitFill

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq (MemoryInit.code name h) (.seq FillSetup.code (FillFinish.code name h))

end VG.Impl.Argon2.AArch64.InitFill
