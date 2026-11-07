module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.Mont.X86.Exponent

/-! # Public RSA exponentiation that stops after the exponent's top bit

The exponent at header offset 128 is public, so each iteration branches on
its low bit, multiplying the result by the base only for a set bit, and the
loop ends once no set bit is left: for `e = 65537`, seventeen squares and two
multiplications, rather than `exponentiate`'s 64 of each.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86

/-- The public exponent, in two 32-bit words. -/
def exponentOffset : Nat := 128

/-- ZF is set exactly when the exponent's low bit is clear. -/
def bitTest : List Instr :=
  [.mov .ecx (.mem (sc exponentOffset)), .alu .and .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

/-- ZF is set exactly when no bit of the exponent is left. -/
def exponentLeft : List Instr :=
  [.mov .eax (.mem (sc exponentOffset)), .alu .or .eax (.mem (sc (exponentOffset + 4))),
   .alu .cmp .eax (.imm 0)]

end VG.Impl.Bignum.X86.PublicContext
