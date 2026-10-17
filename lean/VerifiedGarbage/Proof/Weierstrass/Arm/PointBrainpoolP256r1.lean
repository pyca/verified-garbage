module

public import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.BrainpoolP256r1
meta import VerifiedGarbage.Spec.BrainpoolP256r1
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519
meta import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Spec.X25519

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: brainpoolP256r1

brainpoolP256r1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`ModOk`), and the
functions' constant time by taint tracking, from the pointer's register
(`r0`) public. Apart from the other curves', so that adding it rebuilds none
of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont Spec.Weierstrass.Point

theorem brainpoolp256r1_add_ct :
    ConstantTime isa (sumArm brainpoolp256r1 false).pre (sumArm brainpoolp256r1 false).pub
      (fn (modP brainpoolp256r1) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1_double_ct :
    ConstantTime isa (sumArm brainpoolp256r1 true).pre (sumArm brainpoolp256r1 true).pub
      (fn (modP brainpoolp256r1) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1_add_verified (hF : Fermat brainpoolp256r1.p) :
    Verified Arm.target (pointAdd brainpoolp256r1) (brainpoolp256r1.addContract Arm.abi) :=
  sum_verified brainpoolp256r1 Mont.brainpoolp256r1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    brainpoolp256r1_add_ct

theorem brainpoolp256r1_double_verified (hF : Fermat brainpoolp256r1.p) :
    Verified Arm.target (pointDouble brainpoolp256r1) (brainpoolp256r1.doubleContract Arm.abi) :=
  sum_verified brainpoolp256r1 Mont.brainpoolp256r1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true
    brainpoolp256r1_double_ct

end VG.Proof.Weierstrass.Arm.Point
