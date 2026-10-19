module

public import VerifiedGarbage.Impl.Bignum.X86.PublicExponent

/-! # Public RSA exponentiation that stops after the exponent's top bit

The exponent at header offset 128 is public, so each iteration branches on
its low bit, multiplying the result by the base only for a set bit, and the
loop ends once no set bit is left: for `e = 65537`, seventeen squares and two
multiplications, rather than `exponentiate`'s 64 of each.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86

/-- ZF is set exactly when the exponent's low bit is clear. -/
def bitTest : List Instr :=
  [.mov .ecx (.mem (sc exponentOffset)), .alu .and .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

/-- ZF is set exactly when no bit of the exponent is left. -/
def exponentLeft : List Instr :=
  [.mov .eax (.mem (sc exponentOffset)), .alu .or .eax (.mem (sc (exponentOffset + 4))),
   .alu .cmp .eax (.imm 0)]

def sparseProduct (n : Nat) : Prog isa :=
  .seq (.block bitTest) (.ite .e (.block []) (multiply n 7 7 6))

def sparseRound (n : Nat) : Prog isa :=
  .seq (sparseProduct n)
    (.seq (multiply n 6 6 6) (.block (Dynamic.shiftExponent 2 exponentOffset ++ exponentLeft)))

/-- Input in array six; output in array seven. One and R² come from setup. -/
def sparseExponentiate (n : Nat) : Prog isa :=
  .seq (multiply n 7 5 4)
    (.seq (multiply n 6 6 5) (.seq (.loop (sparseRound n) .ne) (multiply n 7 7 4)))

end VG.Impl.Bignum.X86.PublicContext
