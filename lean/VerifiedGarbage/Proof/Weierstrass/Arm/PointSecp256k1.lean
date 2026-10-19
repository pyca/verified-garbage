module

public import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
meta import VerifiedGarbage.Impl.Secp256k1.Point

import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.Arm.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Row
meta import VerifiedGarbage.Proof.Mont.Arm.Step
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
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
