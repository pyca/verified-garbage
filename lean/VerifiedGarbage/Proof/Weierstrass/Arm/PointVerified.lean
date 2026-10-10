import VerifiedGarbage.Proof.Weierstrass.Arm.PointContract
import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: verified

`pointAdd C` and `pointDouble C` meet the contracts of their `Api`s
(`add_verified`, `double_verified`): the proof against `sumArm`, which it
implies, given its constant time (proven for each curve by taint tracking:
only the pointer, in `r0`, is public), and a state satisfying it (`satPt`:
every number 0).
-/

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont

/-- `addContract` (`dbl` false) or `doubleContract`. -/
def sumC (C : Spec.Weierstrass.Point.Curve) (dbl : Bool) : Contract Arm.isa :=
  Spec.Weierstrass.Point.sig.contract Arm.abi (pre := fun ws m => C.sumPre (Spec.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ws m)
    (post := fun ws m m' _ => C.sumPost (Spec.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ws m m')

/-- A state satisfying the preconditions. -/
def satPt : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-- Zero memory satisfies the precondition. -/
theorem pre_zero (C : Spec.Weierstrass.Point.Curve) (hp : 0 < C.p) (ws : Addr) (q : Nat) :
    C.Below (C.pointAt (fun _ => 0) ws (Spec.Weierstrass.Point.pAt C.k)) ∧ C.Below (C.pointAt (fun _ => 0) ws q) ∧
      C.ConstsBelow ws (fun _ => 0) := by
  have hz : ∀ o, C.coordAt (fun _ => 0) ws o = 0 := fun o => numAt_zero _ _ _
  simp only [Spec.Weierstrass.Point.Curve.Below, Spec.Weierstrass.Point.Curve.pointAt, Spec.Weierstrass.Point.Curve.ConstsBelow, hz]
  omega

theorem sat_pre (C : Spec.Weierstrass.Point.Curve) (hp : 0 < C.p) (dbl : Bool) :
    (sumC C dbl).pre satPt :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.Weierstrass.Point.sig, Arm.abi, Arm.argRegs, Arm.Loc.val, satPt]
    exact ⟨by decide, pre_zero C hp _ _⟩)

/-- `vg_<curve>_point_add` (`dbl` false) or `vg_<curve>_point_double` meets
its contract, given its constant time. -/
theorem sum_verified (C : Spec.Weierstrass.Point.Curve) (hM : Mont.ModOk C.k C.p) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (dbl : Bool)
    (hct : ConstantTime isa (sumArm C dbl).pre (sumArm C dbl).pub (fn (modP C) dbl)) :
    Verified Arm.target (fn (modP C) dbl) (sumC C dbl) :=
  Verified.of_correct (sum_arm hM hk6 hodd h1 hF dbl) hct
    { pre := by sig_implies_pre [sumC, Spec.Weierstrass.Point.Curve.sumPre, Spec.Weierstrass.Point.Curve.sumPost, Spec.Weierstrass.Point.sig, sumArm, Spec.Weierstrass.Point.Curve.ConstsBelow, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [sumC, Spec.Weierstrass.Point.Curve.sumPre, Spec.Weierstrass.Point.Curve.sumPost, Spec.Weierstrass.Point.sig, sumArm, Spec.Weierstrass.Point.Curve.ConstsBelow, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [sumC, Spec.Weierstrass.Point.Curve.sumPre, Spec.Weierstrass.Point.Curve.sumPost, Spec.Weierstrass.Point.sig, sumArm, Spec.Weierstrass.Point.Curve.ConstsBelow, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satPt, sat_pre C (by omega) dbl⟩ }

end VG.Proof.Weierstrass.Arm.Point
