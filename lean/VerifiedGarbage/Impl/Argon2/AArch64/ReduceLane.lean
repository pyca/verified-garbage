module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Impl.Argon2.AArch64.ReducePointers
public import VerifiedGarbage.Impl.Argon2.AArch64.ReduceBlock

/-! Accumulate one lane's last block into matrix block zero. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.ReduceLane

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .seq ReducePointers.code ReduceBlock.code

end VG.Impl.Argon2.AArch64.ReduceLane
