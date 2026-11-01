module

import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
public import VerifiedGarbage.Proof.Weierstrass.Point0Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
public import VerifiedGarbage.Proof.Weierstrass.X86.PointContract

/-!
# Doubling and affine addition for `a = 0` as functions, on x86 (32-bit)

`fn0 (modP C) dbl` (`Impl/Weierstrass/X86/Point.lean`: `fnOps` with
Algorithm 9 if `dbl`, else Algorithm 8) meets the contracts of
`Proof/Weierstrass/Point0Contract.lean` (`double0Contract`, `add0mContract`), as
`fn` meets `point_double`'s and `point_add`'s: from `sumX86`'s
precondition (`pt0X86`), by `fnOps_ok`, with `O`'s coordinates standing for
`rcbDbl0` or `rcbAdd0m` of what `3b` and the operands stand for
(`pt0_x86`), and verified given its constant time (`pt0_verified`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86.Point
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Mont
open VG.Proof.Weierstrass.Point (Fermat qOf dec_eq)

/-- What the formulas for `a = 0` compute from `3b` and the operands. -/
def val0 (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) (ws : Addr) (m : Mem) :
    Fin C.p × Fin C.p × Fin C.p :=
  if dbl then C.dbl0 ws m else C.add0m ws m

/-- `vg_<curve>_point_a0_double(ws)` (`dbl`) or `vg_<curve>_point_a0_add_affine`. -/
def pt0X86 (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) : Contract X86.isa where
  pre := (sumX86 C dbl).pre
  post s s' :=
    C.Below (C.pointAt s'.mem (wsOf s) (Impl.Weierstrass.Point.oAt C.k)) ∧
    C.decPt (C.pointAt s'.mem (wsOf s) (Impl.Weierstrass.Point.oAt C.k)) = val0 C dbl (wsOf s) s.mem ∧
    Impl.Weierstrass.Point.Keeps C.k (wsOf s) s.mem s'.mem
  pub := (sumX86 C dbl).pub

/-- `fn0 (modP C) dbl` meets its contract, by register. -/
theorem pt0_x86 {C : Impl.Weierstrass.Point.Curve} (hF : FnOk (modP C)) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hFe : Fermat C.p) (dbl : Bool) (s : State)
    (hs : (pt0X86 C dbl).pre s) :
    ∃ t s', Exec isa (fn0 (modP C) dbl) s t s' ∧ abiPreserved s s' ∧ (pt0X86 C dbl).post s s' := by
  have hp := prePt_of hk3 hk6 hs
  have hl := lay_nums hk3 hk6
  obtain ⟨t, s', he, A, O, hlt, hEq⟩ := fnOps_ok (S := modP C) hF hodd (ops0_opsOk dbl) hp
  have hu : UnitMod C.p C.R := unitMod_pow_two hodd _
  have dq := dec_eq C h1 hFe hu
  have e : ∀ (m : Mem) x, x < 4096 → C.coordAt m (wsOf s) x = wordsVal m (wsOf s) x C.k :=
    fun m x hx => coordAt_eq C _ _ (by omega_arith)
  have e2 : Impl.Weierstrass.Point.elemBytes C.k * 2 = 2 * Impl.Weierstrass.Point.elemBytes C.k := by omega_arith
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_outs hk3 hk6 O⟩
  · have h0 := hlt 0 (by decide); have h1' := hlt 1 (by decide); have h2 := hlt 2 (by decide)
    simp only [enc, Nat.reduceLT, ↓reduceIte, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h0 h1' h2
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Impl.Weierstrass.Point.Curve.pointAt]
    · rw [e _ _ (by omega_arith)]; exact h0
    · rw [e _ _ (by omega_arith)]; exact h1'
    · rw [e _ _ (by omega_arith)]; rw [e2] at h2; exact h2
  · rw [ops0_run] at hEq
    simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, E₀, e2] at hEq
    simp only [Impl.Weierstrass.Point.Curve.decPt, Impl.Weierstrass.Point.Curve.pointAt, val0,
      Impl.Weierstrass.Point.Curve.dbl0, Impl.Weierstrass.Point.Curve.add0m,
      Impl.Weierstrass.Point.Curve.b3, dq]
    cases dbl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hEq ⊢ <;>
      (repeat rw [e _ _ (by omega_arith)]) <;>
      exact hEq

/-- `double0Contract` (`dbl`) or `add0mContract`, for 20 bytes of stack. -/
def pt0C (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) : Contract X86.isa :=
  if dbl then C.double0Contract X86.abi 20 else C.add0mContract X86.abi 20

/-- The contract implies `pt0X86`, and `satPt` satisfies it. -/
theorem pt0_implies (C : Impl.Weierstrass.Point.Curve) (hp : 0 < C.p) (dbl : Bool) :
    (pt0X86 C dbl).Implies (pt0C C dbl) := by
  cases dbl
  all_goals exact {
    pre := by sig_implies_pre [pt0C, Impl.Weierstrass.Point.Curve.double0Contract,
      Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.Curve.sumPre,
      Impl.Weierstrass.Point.Curve.resultPost, Impl.Weierstrass.Point.sig, pt0X86, sumX86, val0, qOf,
      Impl.Weierstrass.Point.Curve.ConstsBelow, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    post := by sig_implies_post [pt0C, Impl.Weierstrass.Point.Curve.double0Contract,
      Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.Curve.sumPre,
      Impl.Weierstrass.Point.Curve.resultPost, Impl.Weierstrass.Point.sig, pt0X86, sumX86, val0, qOf,
      Impl.Weierstrass.Point.Curve.ConstsBelow, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    pub := by sig_implies_pub [pt0C, Impl.Weierstrass.Point.Curve.double0Contract,
      Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.Curve.sumPre,
      Impl.Weierstrass.Point.Curve.resultPost, Impl.Weierstrass.Point.sig, pt0X86, sumX86, val0, qOf,
      Impl.Weierstrass.Point.Curve.ConstsBelow, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    sat := ⟨satPt, by
      simp only [pt0C, Bool.false_eq_true, ↓reduceIte]
      exact Sig.contract_pre_of_check (by decide +kernel) (by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Point.sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        try simp only [arg_sat]
        exact ⟨by decide, pre_zero C hp _ _⟩)⟩ }

/-- `vg_<curve>_point_a0_double` (`dbl`) or `vg_<curve>_point_a0_add_affine`
meets its contract, given its constant time. -/
theorem pt0_verified (C : Impl.Weierstrass.Point.Curve) (hF : FnOk (modP C)) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hFe : Fermat C.p) (dbl : Bool)
    (hct : ConstantTime isa (pt0X86 C dbl).pre (pt0X86 C dbl).pub (fn0 (modP C) dbl)) :
    Verified X86.target (fn0 (modP C) dbl) (pt0C C dbl) :=
  Verified.of_correct (pt0_x86 hF hk3 hk6 hodd h1 hFe dbl) hct (pt0_implies C (by omega) dbl)

end VG.Proof.Weierstrass.X86.Point
