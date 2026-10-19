module
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract

import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
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

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: brainpoolP384r1

brainpoolP384r1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`ModOk`), and the
functions' constant time by taint tracking, from the pointer's register
(`r0`) public. Apart from the other curves', so that adding it rebuilds none
of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont Spec.Weierstrass.Point

theorem brainpoolp384r1_add_ct :
    ConstantTime isa (sumArm brainpoolp384r1 false).pre (sumArm brainpoolp384r1 false).pub
      (fn (modP brainpoolp384r1) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1_double_ct :
    ConstantTime isa (sumArm brainpoolp384r1 true).pre (sumArm brainpoolp384r1 true).pub
      (fn (modP brainpoolp384r1) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1_add_verified (hF : Fermat brainpoolp384r1.p) :
    Verified Arm.target (pointAdd brainpoolp384r1) (brainpoolp384r1.addContract Arm.abi) :=
  sum_verified brainpoolp384r1 Mont.brainpoolp384r1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false
    brainpoolp384r1_add_ct

theorem brainpoolp384r1_double_verified (hF : Fermat brainpoolp384r1.p) :
    Verified Arm.target (pointDouble brainpoolp384r1) (brainpoolp384r1.doubleContract Arm.abi) :=
  sum_verified brainpoolp384r1 Mont.brainpoolp384r1p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true
    brainpoolp384r1_double_ct

end VG.Proof.Weierstrass.Arm.Point
