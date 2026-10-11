module

public import VerifiedGarbage.Impl.P256.VerifyArithmetic
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.ArithmeticAdd
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

/-- Complete public addition with register-forwarded field blocks. -/
def add (K : WinCfg) (p q o : Pt) : Prog isa :=
  .seq (.block (zeroMask K.M.n p.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o q)) <|
  .seq (.block (zeroMask K.M.n q.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o p)) <|
  .seq (VG.Impl.P256.VerifyArithmetic.program K.M (jacHead K.S p q)) <|
  .seq (.block (zeroMask K.M.n K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask K.M.n K.S.t5)) <|
      .ite (.nonzero .x .x2) (VG.Impl.P256.VerifyDouble.double K.M K.S p o) (.block (infinity K o)))
    (VG.Impl.P256.VerifyArithmetic.program K.M (jacTail K.S p q o))

end VG.Impl.Weierstrass.AArch64.ArithmeticAdd
