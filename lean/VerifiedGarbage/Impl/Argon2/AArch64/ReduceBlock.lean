module
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions


/-! XOR a last-lane block at `x1` into the accumulator at `x0`: eight words
per pass of a loop counted down in `x14`, advancing both pointers, which are
restored at the end. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.ReduceBlock

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def word (i : Nat) : List Instr :=
  [.ldr .x .x8 .x1 (8 * i), .ldr .x .x13 .x0 (8 * i), .logic .eor .x .x8 .x8 .x13,
    .str .x .x8 .x0 (8 * i)]

def words (n : Nat) : List Instr := (List.range n).flatMap word

def setup : List Instr := [.movz .x .x14 16 0]

def advance : List Instr := [.addImm .x .x0 .x0 64, .addImm .x .x1 .x1 64, .subImm .x .x14 .x14 1]

def restore : List Instr := [.subImm .x .x0 .x0 1024, .subImm .x .x1 .x1 1024]

def body : Prog isa := .seq (.block (words 8)) (.block advance)

def code : Prog isa :=
  .seq (.block setup) (.seq (.loop body (.nonzero .x .x14)) (.block restore))

end VG.Impl.Argon2.AArch64.ReduceBlock
