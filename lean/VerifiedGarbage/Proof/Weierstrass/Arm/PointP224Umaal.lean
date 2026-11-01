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
# P-224's point addition and doubling with `umaal`, on 32-bit ARM: verified

`vg_p224_point_add_umaal` and `vg_p224_point_double_umaal`, whose field
multiplications are calls of `vg_p224_mul_mod_p_umaal`, meet the contracts
of `vg_p224_point_add` and `vg_p224_point_double` (`sum_verified`), constant
time by taint tracking with `umaal` (`taintU`). Apart from the other curves',
so that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point Spec.Weierstrass.Point Impl.Weierstrass.Point

theorem p224_addU_ct : ConstantTime isa (sumArm p224 false).pre (sumArm p224 false).pub (fn (modP p224) false true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p224_doubleU_ct : ConstantTime isa (sumArm p224 true).pre (sumArm p224 true).pub (fn (modP p224) true true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p224_addU_verified (hF : Fermat p224.p) :
    Verified Arm.target (pointAdd p224 true) (p224.addContract Arm.abi) :=
  sum_verified p224 Mont.p224p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false p224_addU_ct

theorem p224_doubleU_verified (hF : Fermat p224.p) :
    Verified Arm.target (pointDouble p224 true) (p224.doubleContract Arm.abi) :=
  sum_verified p224 Mont.p224p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true p224_doubleU_ct

end VG.Proof.Weierstrass.Arm.Point
