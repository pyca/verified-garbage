import VerifiedGarbage.Impl.P256.VerifyArithmetic
import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian


namespace VG.Impl.Weierstrass.AArch64.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

def mixedAdd (K : WinCfg) (p q o : Pt) : Prog isa :=
  let head := jacMixedHead K.S p q
  let tail := jacMixedTail K.S p q o
  .seq (.block (zeroMask K.M.n p.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y)) <|
  .seq (VG.Impl.P256.VerifyArithmetic.program K.M head) <|
  .seq (.block (zeroMask K.M.n K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask K.M.n K.S.t5)) <|
      .ite (.nonzero .x .x2) (VG.Impl.P256.VerifyDouble.double K.M K.S p o) (.block (infinity K o)))
    (VG.Impl.P256.VerifyArithmetic.program K.M tail)

end VG.Impl.Weierstrass.AArch64.Joint
