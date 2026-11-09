module
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-!
# The Jacobian window method on x86-64: facts for an iteration

The recoding's offset `16 Σ_{j<J} 32^j` (`offset_eq`), the invariant of the
iterations (`JInv`), `R`'s and `T`'s slots apart from what `D = R + T`
writes (`cadd_apart`), and the masks' choice in the field (`tmv_sel`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- `16 Σ_{j<J} 32^j`. -/
theorem offset_eq (J : Nat) : JacWinCfg.offset J = 16 * Window5.geom J := by
  have := Window5.geom_mul J
  unfold JacWinCfg.offset
  omega_arith

/-- The loop's invariant at `rbx = j`: `R` is a triple of a point of the curve,
`[winE k' J j]P` for `k < n`. -/
structure JInv (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k : Nat) (j : Nat) (s : State) : Prop where
  st : ∃ Q : Point C, onCurve C Q = true ∧
    (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom K.J) K.J j) P) ∧
    RSt K C base size P s₀ Q s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j

/-- `R`'s and `T`'s slots are apart from what `D = R + T` writes. -/
theorem cadd_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], ∀ y ∈ rcbW K.S K.D,
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  intro x hx y hy
  have hyo : y ∈ jwOther K := by
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  simp only [hL.Tx, hL.Ty, hL.Tz, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 0) (j := 7) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 8) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 9) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 10) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 11) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 12) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 5) (by decide) (by decide) (by decide)
  · simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 1) (j := 7) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 8) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 9) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 10) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 11) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 12) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 5) (by decide) (by decide) (by decide)
  · simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 2) (j := 7) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 8) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 9) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 10) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 11) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 12) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 5) (by decide) (by decide) (by decide)
  all_goals exact (hL.jg_apart (List.mem_append_right _ hyo) (by decide)).symm

/-- The masks' choice, in the field. -/
theorem tmv_sel {m0 : Prop} [Decidable m0] {n : Nat} {wz a b c : Nat}
    {Z A B D : Fe C} (hz : wz = 0 ↔ Z = 0)
    (ha : toM C.p (2 ^ (64 * n)) a = A) (hb : toM C.p (2 ^ (64 * n)) b = B)
    (hc : toM C.p (2 ^ (64 * n)) c = D) :
    toM C.p (2 ^ (64 * n)) (if m0 then a else if wz = 0 then b else c) =
      if m0 then A else if Z = 0 then B else D := by
  by_cases h0 : m0
  · simp [h0, ha]
  · by_cases h : wz = 0
    · simp [h0, h, hz.mp h, hb]
    · have hZ : ¬ Z = 0 := fun e => h (hz.mpr e)
      simp [h0, h, hZ, hc]

end VG.Proof.Weierstrass.X86_64
