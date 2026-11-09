module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd

/-! Public-data mixed Jacobian addition retains a common field environment. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure JointMixedChecks (K : WinCfg) (p q o : Pt) : Prop where
  zero : ∀ a∈[p.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyQ : FieldCT (.block (copyPt K.M.n o q))
  init : FieldCT (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y))
  head : FieldCT (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedHead K.S p q))
  tail : FieldCT (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedTail K.S p q o))
  double : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S p o)
  infinity : FieldCT (.block (Jacobian.infinity K o))

end VG.Proof.Weierstrass.AArch64
