module

public import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract

import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
public import VerifiedGarbage.Proof.Weierstrass.Arm.Point0
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Secp256k1.Point
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Point0
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: secp256k1

secp256k1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`ModOk`), and the
functions' constant time by taint tracking, from the pointer's register
(`r0`) public, and so are the functions for `a = 0` (`Point0.lean`). Apart
from the other curves', so that adding it rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG.Impl.Secp256k1 (point)

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont Spec.Weierstrass.Point Impl.Weierstrass.Point

theorem secp256k1_add_ct :
    ConstantTime isa (sumArm point false).pre (sumArm point false).pub
      (fn (modP point) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem secp256k1_add_verified (hF : Fermat point.p) :
    Verified Arm.target (pointAdd point) (point.addContract Arm.abi) :=
  sum_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    secp256k1_add_ct

theorem secp256k1_double0_ct :
    ConstantTime isa (pt0Arm point true).pre (pt0Arm point true).pub (fn0 (modP point) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree (C := point) (dbl := true) hp)) (by native_taint_decide)

theorem secp256k1_add0m_ct :
    ConstantTime isa (pt0Arm point false).pre (pt0Arm point false).pub (fn0 (modP point) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree (C := point) (dbl := false) hp)) (by native_taint_decide)

theorem secp256k1_double0_verified (hF : Fermat point.p) :
    Verified Arm.target (pointDouble0 point) (point.double0Contract Arm.abi) :=
  pt0_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true
    secp256k1_double0_ct

theorem secp256k1_add0m_verified (hF : Fermat point.p) :
    Verified Arm.target (pointAdd0m point) (point.add0mContract Arm.abi) :=
  pt0_verified point Mont.secp256k1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    secp256k1_add0m_ct

end VG.Proof.Weierstrass.Arm.Point
