module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Fixed-time unsigned division on PPC64LE

`r4` holds the numerator, below 2³², and `r5` the positive divisor, below
2³¹. Each of the 32 bits, from the most significant, takes the same eleven
instructions: the next numerator bit (bit 31 of `r4`, which then shifts
left) is added to the doubled remainder in `r7`, the divisor is subtracted
into `r8`, whose bit 63 is then the borrow (the remainder is below 2³²); the
quotient bit, 1 (in `r9`) less the borrow, is added to the doubled quotient
in `r6`, and that bit times the divisor is subtracted from the remainder.
The quotient ends in `r6` and the remainder in `r7`. There are no branches
and no memory accesses, so the numerator may be secret.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Divide

open VG.PPC64LE

/-- One bit of the division by `r5`. -/
def bit : List Instr :=
  [.lsr .w .r8 .r4 31, .lsl .r4 .r4 1, .lsl .r7 .r7 1, .add .r7 .r7 .r8, .sub .r8 .r7 .r5,
    .lsr .d .r8 .r8 63, .sub .r8 .r9 .r8, .lsl .r6 .r6 1, .add .r6 .r6 .r8, .mul .r8 .r8 .r5,
    .sub .r7 .r7 .r8]

/-- `n` bits. -/
def bits : Nat → List Instr
  | 0 => []
  | n + 1 => bits n ++ bit

def code : List Instr := [.li .r6 0, .li .r7 0, .li .r9 1] ++ bits 32

end VG.Impl.Argon2.PPC64LE.Divide
