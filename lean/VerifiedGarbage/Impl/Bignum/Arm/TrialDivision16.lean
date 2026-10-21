module

public import VerifiedGarbage.TCB.Arm.Isa

/-! Small-divisor reduction shared by RSA and FFDH parameter generation.
The caller supplies an odd divisor in r3 and its negative inverse modulo
2^16 in r4. Digits are consumed least significant first. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.TrialDivision16
open VG VG.Arm

/-- One Newton iteration for the inverse of the odd divisor in r3. -/
def newton : List Instr :=
  [.mul .r5 .r3 .r4, .mov .r6 (.imm 2), .dp .sub .r5 .r6 (.reg .r5), .mul .r4 .r4 .r5]

/-- Reduce the caller-selected digit and accumulator by one radix-2^16 step.
The divisor and inverse are in r3/r4, with r6 as temporary.
For divisor s and accumulator below 2s, the new accumulator is below 2s
and satisfies new * 2^16 ≡ digit + old (mod s). -/
def redcAt (acc digit : Reg) : List Instr :=
  [.dp .add digit digit (.reg acc), .mul .r6 digit .r4, .mov .r6 (.shifted .r6 .lsl 16),
    .mov .r6 (.shifted .r6 .lsr 16), .mul .r6 .r6 .r3,
    .dp .add .r6 .r6 (.reg digit), .mov acc (.shifted .r6 .lsr 16)]


/-- The shared RSA/FFDH single-accumulator assignment. -/
def redc : List Instr := redcAt .r2 .r5

end VG.Impl.Bignum.Arm.TrialDivision16
