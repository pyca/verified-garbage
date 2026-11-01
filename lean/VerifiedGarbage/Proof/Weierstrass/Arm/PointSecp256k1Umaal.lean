module

public import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract

import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
public import VerifiedGarbage.Proof.Weierstrass.Arm.Point0
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Secp256k1.Point
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointSecp256k1
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Point0
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# secp256k1's point functions with `umaal`, on 32-bit ARM: verified

`vg_secp256k1_point_add_umaal`, `vg_secp256k1_point_a0_double_umaal` and
`vg_secp256k1_point_a0_add_affine_umaal`, whose field multiplications are
calls of `vg_secp256k1_mul_mod_p_umaal`, meet the contracts of the functions
without the suffix (`sum_verified`, `pt0_verified`), constant time by taint
tracking with `umaal` (`taintU`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG.Impl.Secp256k1 (point)

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont Spec.Weierstrass.Point Impl.Weierstrass.Point

theorem secp256k1_addU_ct :
    ConstantTime isa (sumArm point false).pre (sumArm point false).pub
      (fn (modP point) false true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem secp256k1_addU_verified (hF : Fermat point.p) :
    Verified Arm.target (pointAdd point true) (point.addContract Arm.abi) :=
  sum_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    secp256k1_addU_ct

theorem secp256k1_double0U_ct :
    ConstantTime isa (pt0Arm point true).pre (pt0Arm point true).pub (fn0 (modP point) true true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree (C := point) (dbl := true) hp)) (by taint_decide)

theorem secp256k1_add0mU_ct :
    ConstantTime isa (pt0Arm point false).pre (pt0Arm point false).pub (fn0 (modP point) false true) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree (C := point) (dbl := false) hp)) (by taint_decide)

theorem secp256k1_double0U_verified (hF : Fermat point.p) :
    Verified Arm.target (pointDouble0 point true) (point.double0Contract Arm.abi) :=
  pt0_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true
    secp256k1_double0U_ct

theorem secp256k1_add0mU_verified (hF : Fermat point.p) :
    Verified Arm.target (pointAdd0m point true) (point.add0mContract Arm.abi) :=
  pt0_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    secp256k1_add0mU_ct

end VG.Proof.Weierstrass.Arm.Point
