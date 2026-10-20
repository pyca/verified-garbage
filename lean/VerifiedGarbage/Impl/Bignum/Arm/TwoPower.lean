module

public import VerifiedGarbage.TCB.Arm.Isa

/-! The complete u64 word 2^(t mod 64), built by RSA's five masked shifts.
Input t is in r1; output is r2 (low), r3 (high), with r4 scratch. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.TwoPower
open VG VG.Arm

def step (j : Nat) : List Instr :=
  (if j = 0 then [.dp .and .r3 .r1 (.imm 1)] else [.mov .r3 (.shifted .r1 .lsr j), .dp .and .r3 .r3 (.imm 1)]) ++
  [.mov .r4 (.imm 0), .dp .sub .r3 .r4 (.reg .r3), .mov .r4 (.shifted .r2 .lsl (2 ^ j)),
    .dp .eor .r4 .r4 (.reg .r2), .dp .and .r4 .r4 (.reg .r3), .dp .eor .r2 .r2 (.reg .r4)]

/-- Construct both halves without a data-dependent loop. -/
def code : List Instr :=
  [.dp .and .r1 .r1 (.imm 63), .mov .r2 (.imm 1)] ++ step 0 ++ step 1 ++ step 2 ++
  step 3 ++ step 4 ++
  [.mov .r3 (.shifted .r1 .lsr 5), .dp .and .r3 .r3 (.imm 1), .mov .r4 (.imm 0), .dp .sub .r3 .r4 (.reg .r3),
    .dp .and .r3 .r2 (.reg .r3), .dp .eor .r2 .r2 (.reg .r3)]

end VG.Impl.Bignum.Arm.TwoPower
