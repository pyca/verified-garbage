import VerifiedGarbage.Proof.Weierstrass.X86.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): verified

`pointAdd C` and `pointDouble C` meet the contracts of their `Api`s, for
calls using 20 bytes of stack (`sum_verified`): the proof against `sumX86`,
which it implies, given its constant time (proven for each curve by taint
tracking: only the stack pointer and the argument are public), and a state
satisfying it (`satPt`: every number 0).
-/

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.Impl.Weierstrass.X86.Point VG.Proof.Weierstrass.X86.Mont
open VG.Proof.Weierstrass.Point (Fermat qOf)

/-- `addContract` (`dbl` false) or `doubleContract`, for 20 bytes of stack. -/
def sumC (C : Spec.Weierstrass.Point.Curve) (dbl : Bool) : Contract X86.isa :=
  Spec.Weierstrass.Point.sig.contract X86.abi
    (pre := fun ws m => C.sumPre (Spec.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ws m)
    (post := fun ws m m' _ => C.sumPost (Spec.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ws m m') (stack := 20)

/-- A state satisfying the preconditions: `ws` at address 0, the argument at
`0x20004`, every number 0. -/
def satPt : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20004, 4⟩]
  wr := [⟨0, 8192⟩]

/-- Zero memory satisfies the precondition. -/
theorem pre_zero (C : Spec.Weierstrass.Point.Curve) (hp : 0 < C.p) (ws : Addr) (q : Nat) :
    C.Below (C.pointAt (fun _ => 0) ws (Spec.Weierstrass.Point.pAt C.k)) ∧ C.Below (C.pointAt (fun _ => 0) ws q) ∧
      C.ConstsBelow ws (fun _ => 0) := by
  have hz : ∀ o, C.coordAt (fun _ => 0) ws o = 0 := fun o => numAt_zero _ _ _
  simp only [Spec.Weierstrass.Point.Curve.Below, Spec.Weierstrass.Point.Curve.pointAt,
    Spec.Weierstrass.Point.Curve.ConstsBelow, hz]
  omega

theorem sat_pre (C : Spec.Weierstrass.Point.Curve) (hp : 0 < C.p) (dbl : Bool) :
    (sumC C dbl).pre satPt :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.Weierstrass.Point.sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    try simp only [arg_sat]
    exact ⟨by decide, pre_zero C hp _ _⟩)

/-- `vg_<curve>_point_add` (`dbl` false) or `vg_<curve>_point_double` meets
its contract, given its constant time. -/
theorem sum_verified (C : Spec.Weierstrass.Point.Curve) (hF : FnOk (modP C)) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hFe : Fermat C.p) (dbl : Bool)
    (hct : ConstantTime isa (sumX86 C dbl).pre (sumX86 C dbl).pub (fn (modP C) dbl)) :
    Verified X86.target (fn (modP C) dbl) (sumC C dbl) :=
  Verified.of_correct (sum_x86 hF hk3 hk6 hodd h1 hFe dbl) hct
    { pre := by sig_implies_pre [sumC, Spec.Weierstrass.Point.Curve.sumPre, Spec.Weierstrass.Point.Curve.sumPost,
        Spec.Weierstrass.Point.sig, sumX86, Spec.Weierstrass.Point.Curve.ConstsBelow, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      post := by sig_implies_post [sumC, Spec.Weierstrass.Point.Curve.sumPre, Spec.Weierstrass.Point.Curve.sumPost,
        Spec.Weierstrass.Point.sig, sumX86, Spec.Weierstrass.Point.Curve.ConstsBelow, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [sumC, Spec.Weierstrass.Point.Curve.sumPre, Spec.Weierstrass.Point.Curve.sumPost,
        Spec.Weierstrass.Point.sig, sumX86, Spec.Weierstrass.Point.Curve.ConstsBelow, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      sat := ⟨satPt, sat_pre C (by omega) dbl⟩ }

end VG.Proof.Weierstrass.X86.Point
