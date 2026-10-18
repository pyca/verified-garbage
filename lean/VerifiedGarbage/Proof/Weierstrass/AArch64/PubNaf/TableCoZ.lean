module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CoZField
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# The public NAF's table by co-Z arithmetic

`R = P` (affine, its `z` one), stored in the first entry; DBLU: `2P` and `P`
at one `Z`, into `E` (`x`, `y`) and `R`; then seven times ZADDU, `R = R + 2P`
with `E` the same `2P` at the new `Z`, stored in the next entry
(`table_ok`): the table holds `[1]P, [3]P, …, [15]P`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The construction after `m` entries, from `s₀`: `R = [2m - 1]P`, `E = 2P`
at `R`'s nonzero `Z`, `x20` at entry `m + 1`. -/
structure CSt (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State)
    (m : Nat) : Prop where
  scr : Scr s base size
  keep : KeepRegs (nafClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : OddTbl K C base P m s
  lt : ∀ x ∈ [K.E.x, K.E.y, K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  d : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.R.z)
    (mul 2 P)
  r : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (2 * m - 1) P)
  z : tmv C K.M.n base s K.R.z ≠ 0
  x20 : s.gpr .x20 = off base (stride K * m)

/-- The co-Z state's slots, written by the loop. -/
theorem coZ_other (K : WinCfg) : ∀ x ∈ [K.E.x, K.E.y, K.R.x, K.R.y, K.R.z], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact E_other K _ (by simp)
  · exact E_other K _ (by simp)
  · exact R_other K _ (by simp)
  · exact R_other K _ (by simp)
  · exact R_other K _ (by simp)

/-- A slot a field program wrote, from its invariant. -/
theorem written_val {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {ops : List FOp}
    {V : List Nat} {E : Nat → Fe C} {t : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) (validAfter ops V) (runOps ops E) t) {x : Nat}
    (hx : x ∈ ops.map FOp.out) :
    tmv C K.M.n base t x = runOps ops E x ∧ wordsVal t.mem base x K.M.n < C.p := by
  have hv : x ∈ validAfter ops V := (mem_validAfter _ _).mpr (Or.inr hx)
  exact ⟨hI.val x hv, hI.lt x hv⟩

theorem out_mem {σ : Nat → Nat} {N : List FOp} {i : Nat} (h : i ∈ N.map FOp.out) :
    σ i ∈ (N.map (FOp.rename σ)).map FOp.out := by
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨_, List.mem_map_of_mem hop, FOp.out_rename ..⟩

/-- ZADDU: `R = R + E`, `E` the same `2P` at the new `Z`. -/
theorem zadduStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C)
    (hn : 17 ≤ C.n) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    {m : Nat} (hm1 : 1 ≤ m) (hm : m ≤ 7) {s : State}
    (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hro : ∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p)
    (hlt : ∀ x ∈ [K.E.x, K.E.y, K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hd : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.R.z)
      (mul 2 P))
    (hr : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul (2 * m - 1) P))
    (hz : tmv C K.M.n base s K.R.z ≠ 0) :
    WP isa (fprogB K.M (zadduOps K)) s fun t =>
      KeepRegs (clob K.M.n) s t ∧ Unch base (loopW K) s.mem t.mem ∧ Scr t base size ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.E.x, K.E.y, K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.R.z)
        (mul 2 P) ∧
      InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z)
        (mul (2 * (m + 1) - 1) P) ∧
      tmv C K.M.n base t K.R.z ≠ 0 := by
  have hW := hL.win
  let V := winRo K ++ [K.E.x, K.E.y, K.R.x, K.R.y, K.R.z]
  have hVs : ∀ x ∈ V, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem (coZ_other K x hx)
  have hVl : ∀ x ∈ V, wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hro x hx
    · exact hlt x hx
  have hv : ∀ i ∈ [0, 1, 8, 9, 10], coZσ K i ∈ V := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [V, coZσ]
  refine WP.mono (coZ_ok hL hp CoZTable.zaddu_out CoZTable.zaddu_reads (inv_of hs hM hVs hVl) hv)
    fun t ⟨kt, Ut, It, et⟩ => ?_
  let e : Nat → Fe C := fun j => tmv C K.M.n base s (coZσ K j)
  have hr' : InvJ C (e 8) (e 9) (e 10) (mul (2 * (m - 1) + 1) P) := by
    rw [show 2 * (m - 1) + 1 = 2 * m - 1 by omega]; exact hr
  obtain ⟨js, jd, jz⟩ := CoZTable.zaddu_pts hC hO hn hM3 hP hP0 (k := m - 1) (by omega) hd hr' hz
  have w : ∀ i ∈ [0, 1, 8, 9, 10], tmv C K.M.n base t (coZσ K i) = runOps CoZ.zaddu e i ∧
      wordsVal t.mem base (coZσ K i) K.M.n < C.p := by
    intro i hi
    have hx : coZσ K i ∈ (CoZ.zaddu.map (FOp.rename (coZσ K))).map FOp.out := out_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
    obtain ⟨v, l⟩ := written_val It hx
    exact ⟨v.trans (et i), l⟩
  obtain ⟨w0, l0⟩ := w 0 (by simp)
  obtain ⟨w1, l1⟩ := w 1 (by simp)
  obtain ⟨w8, l8⟩ := w 8 (by simp)
  obtain ⟨w9, l9⟩ := w 9 (by simp)
  obtain ⟨w10, l10⟩ := w 10 (by simp)
  refine ⟨kt, Ut, It.scr, It.mod, fun x hx => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [l0, l1, l8, l9, l10]
  · change InvJ C (tmv C K.M.n base t (coZσ K 0)) (tmv C K.M.n base t (coZσ K 1))
      (tmv C K.M.n base t (coZσ K 10)) _
    rw [w0, w1, w10]; exact jd
  · change InvJ C (tmv C K.M.n base t (coZσ K 8)) (tmv C K.M.n base t (coZσ K 9))
      (tmv C K.M.n base t (coZσ K 10)) _
    rw [w8, w9, w10, show 2 * (m + 1) - 1 = 2 * (m - 1 + 1) + 1 by omega]; exact js
  · change tmv C K.M.n base t (coZσ K 10) ≠ 0
    rw [w10]; exact jz

end VG.Proof.Weierstrass.AArch64.PubNaf
