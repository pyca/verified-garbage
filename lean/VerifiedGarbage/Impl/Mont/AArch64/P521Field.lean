module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Square

/-! P-521 arithmetic in the ordinary nine-word field representation. -/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P521Field

open VG.AArch64

/-- The symmetric square and canonical Mersenne reduction, without the
Montgomery representation's cyclic rotation. -/
def squareCore : List Instr :=
  P521Square.product ++ P521Square.foldCode ++ P521Square.correctCode

/-- The existing alias-safe square's entry and exit, in ordinary field form. -/
def square : VG.Prog isa :=
  .seq (.block P521Square.entry) (.block (squareCore ++ P521Square.exit))

end VG.Impl.Mont.AArch64.P521Field
