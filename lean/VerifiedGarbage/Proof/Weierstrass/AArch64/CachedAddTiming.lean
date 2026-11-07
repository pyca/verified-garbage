module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddField
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure Checks : Prop where
  zero : ∀ a∈[K.R.z,K.E.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyP : FieldCT (.block (copyPt K.M.n K.D K.R))
  copyQ : FieldCT (.block (copyPt K.M.n K.D K.E))
  head : FieldCT ops.head
  tail : FieldCT ops.tail
  double : FieldCT ops.double
  infinity : FieldCT (.block (Jacobian.infinity K K.D))

end VG.Proof.Weierstrass.AArch64.CachedField
