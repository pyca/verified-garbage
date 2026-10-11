module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
public import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Begin the final reduction at lane zero with a zero accumulator in matrix block zero. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.ReductionInit

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def setup : List Instr := [load .x0 .x19 232, imm .x24 0].flatten

def code : Prog isa := .seq (.block setup) ClearBlock.code

end VG.Impl.Argon2.AArch64.ReductionInit
