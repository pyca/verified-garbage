module
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
public import VerifiedGarbage.Proof.Weierstrass.Law

import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# brainpoolP384r1's point addition and doubling with `umaal`, on 32-bit ARM: verified

`vg_brainpoolp384r1_point_add_umaal` and `vg_brainpoolp384r1_point_double_umaal`, whose field
multiplications are calls of `vg_brainpoolp384r1_mul_mod_p_umaal`, meet the contracts
of `vg_brainpoolp384r1_point_add` and `vg_brainpoolp384r1_point_double` (`sum_verified`), constant
time by taint tracking with `umaal` (`taintU`). Apart from the other curves',
so that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point Spec.Weierstrass.Point Impl.Weierstrass.Point

theorem brainpoolp384r1_addU_ct : ConstantTime isa (sumArm brainpoolp384r1 false).pre (sumArm brainpoolp384r1 false).pub (fn (modP brainpoolp384r1) false true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem brainpoolp384r1_doubleU_ct : ConstantTime isa (sumArm brainpoolp384r1 true).pre (sumArm brainpoolp384r1 true).pub (fn (modP brainpoolp384r1) true true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem brainpoolp384r1_addU_verified (hF : Fermat brainpoolp384r1.p) :
    Verified Arm.target (pointAdd brainpoolp384r1 true) (brainpoolp384r1.addContract Arm.abi) :=
  sum_verified brainpoolp384r1 Mont.brainpoolp384r1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false brainpoolp384r1_addU_ct

theorem brainpoolp384r1_doubleU_verified (hF : Fermat brainpoolp384r1.p) :
    Verified Arm.target (pointDouble brainpoolp384r1 true) (brainpoolp384r1.doubleContract Arm.abi) :=
  sum_verified brainpoolp384r1 Mont.brainpoolp384r1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true brainpoolp384r1_doubleU_ct

end VG.Proof.Weierstrass.Arm.Point
