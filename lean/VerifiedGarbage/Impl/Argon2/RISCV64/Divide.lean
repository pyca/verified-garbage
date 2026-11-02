module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Fixed-time unsigned division on RISC-V

The PPC64LE division (`Impl/Argon2/PPC64LE/Divide.lean`), with its registers
renamed: `a1` holds the numerator, below 2³², and `a2` the positive divisor,
below 2³¹. Each of the 32 bits, from the most significant, takes the same
eleven instructions: the next numerator bit (bit 31 of `a1`, by a 32-bit
shift, which then shifts left) is added to the doubled remainder in `a4`,
the divisor is subtracted into `a5`, whose bit 63 is then the borrow (the
remainder is below 2³²); the quotient bit, 1 (in `a6`) less the borrow, is
added to the doubled quotient in `a3`, and that bit times the divisor is
subtracted from the remainder. The quotient ends in `a3` and the remainder
in `a4`. There are no branches and no memory accesses, so the numerator may
be secret.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Divide

open VG.RISCV64

/-- One bit of the division by `a2`. -/
def bit : List Instr :=
  [.shift .srl .w .a5 .a1 31, .shift .sll .d .a1 .a1 1, .shift .sll .d .a4 .a4 1, .add .a4 .a4 .a5,
    .sub .a5 .a4 .a2, .shift .srl .d .a5 .a5 63, .sub .a5 .a6 .a5, .shift .sll .d .a3 .a3 1,
    .add .a3 .a3 .a5, .mul .a5 .a5 .a2, .sub .a4 .a4 .a5]

/-- `n` bits. -/
def bits : Nat → List Instr
  | 0 => []
  | n + 1 => bits n ++ bit

def code : List Instr := [.li .a3 0, .li .a4 0, .li .a6 1] ++ bits 32

end VG.Impl.Argon2.RISCV64.Divide
