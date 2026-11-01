module
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
public import VerifiedGarbage.Proof.Weierstrass.Law

import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# P-384's point addition and doubling with `umaal`, on 32-bit ARM: verified

`vg_p384_point_add_umaal` and `vg_p384_point_double_umaal`, whose field
multiplications are calls of `vg_p384_mul_mod_p_umaal`, meet the contracts
of `vg_p384_point_add` and `vg_p384_point_double` (`sum_verified`), constant
time by taint tracking with `umaal` (`taintU`). Apart from the other curves',
so that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point Spec.Weierstrass.Point Impl.Weierstrass.Point

theorem p384_addU_ct : ConstantTime isa (sumArm p384 false).pre (sumArm p384 false).pub (fn (modP p384) false true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p384_doubleU_ct : ConstantTime isa (sumArm p384 true).pre (sumArm p384 true).pub (fn (modP p384) true true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p384_addU_verified (hF : Fermat p384.p) :
    Verified Arm.target (pointAdd p384 true) (p384.addContract Arm.abi) :=
  sum_verified p384 Mont.p384p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false p384_addU_ct

theorem p384_doubleU_verified (hF : Fermat p384.p) :
    Verified Arm.target (pointDouble p384 true) (p384.doubleContract Arm.abi) :=
  sum_verified p384 Mont.p384p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true p384_doubleU_ct

end VG.Proof.Weierstrass.Arm.Point
