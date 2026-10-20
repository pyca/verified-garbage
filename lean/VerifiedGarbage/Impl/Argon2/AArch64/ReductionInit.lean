module

public import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock

/-! Begin the final reduction at lane zero with a zero accumulator in matrix block zero.
The accumulator is cleared sixteen words per pass of a loop counted down in
`x9`, advancing `x0`, which is restored at the end. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.ReductionInit

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def setup : List Instr := [load .x0 .x19 232, imm .x24 0].flatten

def clearSetup : List Instr := [.movz .x .x8 0 0, .movz .x .x9 8 0]

def clearAdvance : List Instr := [.addImm .x .x0 .x0 128, .subImm .x .x9 .x9 1]

def clearBody : Prog isa := .seq (.block (ClearBlock.words 16)) (.block clearAdvance)

def clear : Prog isa :=
  .seq (.block clearSetup)
    (.seq (.loop clearBody (.nonzero .x .x9)) (.block [.subImm .x .x0 .x0 1024]))

def code : Prog isa := .seq (.block setup) clear

end VG.Impl.Argon2.AArch64.ReductionInit
