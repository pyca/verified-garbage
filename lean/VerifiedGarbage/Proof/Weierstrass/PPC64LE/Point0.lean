module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
public import VerifiedGarbage.Proof.Weierstrass.Point0Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointContract

/-!
# Doubling and affine addition for `a = 0` as functions, on PPC64LE

`fn0 (modP C) dbl` (`Impl/Weierstrass/PPC64LE/Point.lean`: `fnOps` with
Algorithm 9 if `dbl`, else Algorithm 8) meets the contracts of
`Proof/Weierstrass/Point0Contract.lean` (`double0Contract`, `add0mContract`), as
`fn` meets `point_double`'s and `point_add`'s: from `sumPPC`'s precondition
(`pt0PPC`), by `fnOps_ok`, with `O`'s coordinates standing for `rcbDbl0` or
`rcbAdd0m` of what `3b` and the operands stand for (`pt0_ppc`), and verified
given its constant time (`pt0_verified`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- What the formulas for `a = 0` compute from `3b` and the operands. -/
def val0 (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) (ws : Addr) (m : Mem) :
    Fin C.p × Fin C.p × Fin C.p :=
  if dbl then C.dbl0 ws m else C.add0m ws m

/-- `vg_<curve>_point_a0_double(ws = r3)` (`dbl`) or `vg_<curve>_point_a0_add_affine`. -/
def pt0PPC (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) : Contract PPC64LE.isa where
  pre := (sumPPC C dbl).pre
  post s s' :=
    C.Below (C.pointAt s'.mem (s.gpr .r3) (oAt C.k)) ∧
    C.decPt (C.pointAt s'.mem (s.gpr .r3) (oAt C.k)) = val0 C dbl (s.gpr .r3) s.mem ∧
    Impl.Weierstrass.Point.Keeps C.k (s.gpr .r3) s.mem s'.mem
  pub := (sumPPC C dbl).pub

/-- `fn0 (modP C) dbl` meets its contract, by register. -/
theorem pt0_ppc {C : Impl.Weierstrass.Point.Curve} (hM : ModOk C.k C.p) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (dbl : Bool) (s : State)
    (hs : (pt0PPC C dbl).pre s) :
    ∃ t s', Exec isa (fn0 (modP C) dbl) s t s' ∧ abiPreserved s s' ∧ (pt0PPC C dbl).post s s' := by
  have hp := prePt_of hk3 hk6 hs
  have hl := lay_nums hk3 hk6
  obtain ⟨t, s', he, A, -, O, hlt, hEq⟩ := fnOps_ok (S := modP C) hM hodd (ops0_opsOk dbl) hp
  have hu : UnitMod C.p C.R := unitMod_pow_two hodd _
  have dq := dec_eq C h1 hF hu
  have e : ∀ (m : Mem) x, x < 4096 → C.coordAt m (s.gpr .r3) x = wordsVal m (s.gpr .r3) x C.k :=
    fun m x hx => coordAt_eq C _ _ (by omega)
  have e2 : elemBytes C.k * 2 = 2 * elemBytes C.k := Nat.mul_comm _ _
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_outs hk3 hk6 O⟩
  · have h0 := hlt 0 (by decide); have h1' := hlt 1 (by decide); have h2 := hlt 2 (by decide)
    simp only [enc, Nat.reduceLT, ↓reduceIte, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h0 h1' h2
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Impl.Weierstrass.Point.Curve.pointAt]
    · rw [e _ _ (by omega)]; exact h0
    · rw [e _ _ (by omega)]; exact h1'
    · rw [e _ _ (by omega)]; rw [e2] at h2; exact h2
  · rw [ops0_run] at hEq
    simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, E₀, e2] at hEq
    simp only [Impl.Weierstrass.Point.Curve.decPt, Impl.Weierstrass.Point.Curve.pointAt, val0,
      Impl.Weierstrass.Point.Curve.dbl0, Impl.Weierstrass.Point.Curve.add0m,
      Impl.Weierstrass.Point.Curve.b3, dq]
    cases dbl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hEq ⊢ <;>
      (repeat rw [e _ _ (by omega)]) <;>
      exact hEq

/-- `double0Contract` (`dbl`) or `add0mContract`. -/
def pt0C (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) : Contract PPC64LE.isa :=
  if dbl then C.double0Contract PPC64LE.abi else C.add0mContract PPC64LE.abi

/-- The contract implies `pt0PPC`, and `satPt` satisfies it. -/
theorem pt0_implies (C : Impl.Weierstrass.Point.Curve) (hp : 0 < C.p) (dbl : Bool) :
    (pt0PPC C dbl).Implies (pt0C C dbl) := by
  cases dbl
  all_goals exact {
    pre := by sig_implies_pre [pt0C, Impl.Weierstrass.Point.Curve.double0Contract,
      Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.Curve.sumPre,
      Impl.Weierstrass.Point.Curve.resultPost, Impl.Weierstrass.Point.sig, pt0PPC, sumPPC, val0, qOf,
      Impl.Weierstrass.Point.Curve.ConstsBelow, PPC64LE.abi, PPC64LE.argRegs]
    post := by sig_implies_post [pt0C, Impl.Weierstrass.Point.Curve.double0Contract,
      Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.Curve.sumPre,
      Impl.Weierstrass.Point.Curve.resultPost, Impl.Weierstrass.Point.sig, pt0PPC, sumPPC, val0, qOf,
      Impl.Weierstrass.Point.Curve.ConstsBelow, PPC64LE.abi, PPC64LE.argRegs]
    pub := by sig_implies_pub [pt0C, Impl.Weierstrass.Point.Curve.double0Contract,
      Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.Curve.sumPre,
      Impl.Weierstrass.Point.Curve.resultPost, Impl.Weierstrass.Point.sig, pt0PPC, sumPPC, val0, qOf,
      Impl.Weierstrass.Point.Curve.ConstsBelow, PPC64LE.abi, PPC64LE.argRegs]
    sat := ⟨satPt, by
      simp only [pt0C, Bool.false_eq_true, ↓reduceIte]
      sig_reduce [Sig.wfPre, Impl.Weierstrass.Point.Curve.double0Contract,
        Impl.Weierstrass.Point.Curve.add0mContract, Impl.Weierstrass.Point.sig, PPC64LE.abi,
        PPC64LE.argRegs, satPt]
      refine ⟨trivial, rfl, rfl, by simp, by simp, by simp, ?_⟩
      exact pre_zero C hp _ _⟩ }

/-- `vg_<curve>_point_a0_double` (`dbl`) or `vg_<curve>_point_a0_add_affine`
meets its contract, given its constant time. -/
theorem pt0_verified (C : Impl.Weierstrass.Point.Curve) (hM : ModOk C.k C.p) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (dbl : Bool)
    (hct : ConstantTime isa (pt0PPC C dbl).pre (pt0PPC C dbl).pub (fn0 (modP C) dbl)) :
    Verified PPC64LE.target (fn0 (modP C) dbl) (pt0C C dbl) :=
  Verified.of_correct (pt0_ppc hM hk3 hk6 hodd h1 hF dbl) hct (pt0_implies C (by omega) dbl)

end VG.Proof.Weierstrass.PPC64LE.Point
