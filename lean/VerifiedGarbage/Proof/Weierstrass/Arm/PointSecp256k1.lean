module

public import VerifiedGarbage.Impl.Secp256k1.Point
meta import VerifiedGarbage.Impl.Secp256k1.Point

public import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.Secp256k1
meta import VerifiedGarbage.Spec.Secp256k1
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519
meta import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Spec.X25519

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: secp256k1

secp256k1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`ModOk`), and the
functions' constant time by taint tracking, from the pointer's register
(`r0`) public. Apart from the other curves', so that adding it rebuilds none
of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG.Impl.Secp256k1 (point)

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont Spec.Weierstrass.Point

theorem secp256k1_add_ct :
    ConstantTime isa (sumArm point false).pre (sumArm point false).pub
      (fn (modP point) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem secp256k1_double_ct :
    ConstantTime isa (sumArm point true).pre (sumArm point true).pub
      (fn (modP point) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem secp256k1_add_verified (hF : Fermat point.p) :
    Verified Arm.target (pointAdd point) (point.addContract Arm.abi) :=
  sum_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    secp256k1_add_ct

theorem secp256k1_double_verified (hF : Fermat point.p) :
    Verified Arm.target (pointDouble point) (point.doubleContract Arm.abi) :=
  sum_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true
    secp256k1_double_ct

end VG.Proof.Weierstrass.Arm.Point
