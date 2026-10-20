module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedR2

/-! R-squared setup for a modulus whose highest word is nonzero. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.NormalizedR2
open VG VG.Arm

def constants : Prog isa := .seq (smallConst 4 0) (smallConst 7 2)

/-- Array four is zeroed before setting its highest 64-bit word to one.
The seed is `2^(64*(w-1))`, leaving only `w+64` modular doublings. -/
def top : List Instr :=
  [.ldr .r1 .r0 48, .dp .add .r2 .r1 (.shifted .r1 .lsl 2),
    .mov .r2 (.shifted .r2 .lsl 3), .dp .add .r2 .r2 (.imm 312),
    .dp .add .r2 .r0 (.reg .r2), .mov .r3 (.imm 1), .str .r3 .r2 0]

def count : List Instr :=
  [.ldr .r1 .r0 48, .dp .add .r1 .r1 (.imm 64), .str .r1 .r0 208]

def seed : List Instr := top ++ count

def init : Prog isa := .seq constants (.block seed)

def r2 (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq init (.seq doubleLoop (SharedR2.squares op))

end VG.Impl.Bignum.Arm.NormalizedR2
