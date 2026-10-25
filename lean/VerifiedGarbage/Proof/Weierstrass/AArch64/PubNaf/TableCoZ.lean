module
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State

import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CoZField
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

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
  refine WP.mono (coZ_ok hL hp (coZσ_ren hL.win) CoZTable.zaddu_out CoZTable.zaddu_reads (inv_of hs hM hVs hVl) hv)
    fun t ⟨kt, Ut, It, et⟩ => ?_
  let e : Nat → Fe C := fun j => tmv C K.M.n base s (coZσ K j)
  have hr' : InvJ C (e 8) (e 9) (e 10) (mul (2 * (m - 1) + 1) P) := by
    rw [show 2 * (m - 1) + 1 = 2 * m - 1 by omega_arith]; exact hr
  obtain ⟨js, jd, jz⟩ := CoZTable.zaddu_pts hC hO hn hM3 hP hP0 (k := m - 1) (by omega_arith) hd hr' hz
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
    rw [w8, w9, w10, show 2 * (m + 1) - 1 = 2 * (m - 1 + 1) + 1 by omega_arith]; exact js
  · change tmv C K.M.n base t (coZσ K 10) ≠ 0
    rw [w10]; exact jz

/-- A ZADDU step of the loop: entry `m + 1` holds `[2m + 1]P`. -/
theorem coZStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity) {s₀ : State}
    (hF : NafFixed K C base s₀ P k)
    {m : Nat} (hm1 : 1 ≤ m) (hm : m < 8) {s : State} (h : CSt K C base size P s₀ s m)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (8 - m)) :
    WP isa (tableStep K) s fun t =>
      CSt K C base size P s₀ t (m + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (8 - (m + 1)) := by
  have hW := hL.win
  have hn := h.scr.nowrap
  have h10 : K.M.n < 10 := by have := hL.n6; omega_arith
  rw [tableStep]
  refine WP.seq (WP.mono (zadduStep_ok hL hp hC hM3 hO hn17 hP hP0 hm1 (by omega_arith) h.scr h.mod
    (winRo_lt hW hF h.unch hn) h.lt h.d h.r h.z)
    fun s₂ ⟨k₂, U₂, sc₂, M₂, lt₂, d₂, r₂, z₂⟩ => ?_)
  have x20₂ : s₂.gpr .x20 = off base (stride K * m) := (k₂.gpr _ (x20_not_clob' h10)).trans h.x20
  have x19₂ : s₂.gpr .x19 = BitVec.ofNat 64 (8 - m) := (k₂.gpr _ (x19_not_clob _)).trans h19
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hL sc₂ hm x20₂) fun s₃ ⟨cw, k₃, U₃⟩ => ?_
  have sc₃ := sc₂.of_keepRegs k₃ (by decide)
  have x20₃ : s₃.gpr .x20 = off base (stride K * m) := (k₃.gpr _ (by decide)).trans x20₂
  have x19₃ : s₃.gpr .x19 = BitVec.ofNat 64 (8 - m) := (k₃.gpr _ (by decide)).trans x19₂
  rw [show ([.addImm .x .x20 .x20 (stride K), decCounter] : List Instr) =
    [.addImm .x .x20 .x20 (stride K)] ++ [decCounter] from rfl, WP.block_append_iff]
  have hst : stride K < 4096 := by have := hL.n6; simp only [stride]; omega_arith
  refine WP.mono (addImm_ok s₃ (d := .x20) (n := .x20) hst) fun s₄ ⟨a₄, k₄⟩ => ?_
  have sc₄ := sc₃.of_keeps k₄ (by decide)
  have x19₄ : s₄.gpr .x19 = BitVec.ofNat 64 (8 - m) := (k₄.gpr _ (by decide)).trans x19₃
  refine WP.mono (decCounter_ok s₄ (by omega_arith) (by omega_arith) x19₄) fun t ⟨x19t, kt⟩ => ?_
  have sct := sc₄.of_keeps kt (by decide)
  have m34 : t.mem = s₃.mem := by rw [kt.mem, k₄.mem]
  have U3' := fun {x : Nat} => entry_unch hW (j := m + 1) (by omega_arith) (by omega_arith) U₃ hn (x := x)
  have keepS : ∀ x ∈ winRo K ++ winOther K,
      wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := fun x hx => by
    rw [m34]
    exact U3' (by
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · exact winOther_mem hx) (other_not_tbl hW (by omega_arith) (by omega_arith) hx)
  have tm : ∀ x ∈ winRo K ++ winOther K, tmv C K.M.n base t x = tmv C K.M.n base s₂ x :=
    fun x hx => by show toM _ _ _ = toM _ _ _; rw [keepS x hx]
  have oC : ∀ x ∈ [K.E.x, K.E.y, K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (coZ_other K x hx)
  have T₂ : OddTbl K C base P m s₂ := h.tbl.unch hW (by omega_arith) U₂ hn
  have hU3w : Unch base (winW K) s₂.mem t.mem := by
    rw [m34]
    refine U₃.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, List.mem_append_right _ ?_, by rcases hw with rfl | rfl | rfl <;> rfl⟩
    obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_arith) (by omega_arith) w.1 (by
      rcases hw with rfl | rfl | rfl <;> simp)
    rw [e]; exact winTbl_mem K hi
  refine ⟨⟨sct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h.keep.trans ((k₂.mono clob_nafClob).trans ((k₃.mono (fun r hr => nafClob_mem (by
      simp only [List.mem_singleton] at hr; subst hr; simp))).trans
      ((Keeps.regs k₄).mono (fun r hr => nafClob_mem (by
        simp only [List.mem_singleton] at hr; subst hr; simp)) |>.trans
      ((Keeps.regs kt).mono (fun r hr => nafClob_mem (by
        simp only [List.mem_singleton] at hr; subst hr; simp))))))
  · exact ((h.unch.trans U₂).trans hU3w).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · exact hw
      · exact loopW_sub K w hw
      · exact hw
  · exact M₂.unch hU3w (fun w hw => winW_mo hW M₂ w hw) hn
  · intro a ha1 ham
    rcases Nat.lt_or_ge a (m + 1) with ha | ha
    · obtain ⟨tl, tJ⟩ := T₂ a ha1 (by omega_arith)
      have e : ∀ x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z],
          wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := fun x hx => by
        rw [m34]
        exact U3' (tbl_slot ha1 (by omega_arith) x hx) (tbl_not_tbl hW ha1 (by omega_arith) (by omega_arith) (by omega_arith)
          (by omega_arith) hx)
      refine ⟨fun x hx => by rw [e x hx]; exact tl x hx, ?_⟩
      have et : ∀ x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z],
          tmv C K.M.n base t x = tmv C K.M.n base s₂ x := fun x hx => by
        show toM _ _ _ = toM _ _ _; rw [e x hx]
      rw [et _ (by simp), et _ (by simp), et _ (by simp)]
      exact tJ
    · obtain rfl : a = m + 1 := by omega_arith
      have ec : ∀ c < 3, wordsVal t.mem base (K.tbl + 8 * K.M.n * (3 * m + c)) K.M.n =
          wordsVal s₂.mem base (K.R.x + 8 * K.M.n * c) K.M.n := fun c hc => by rw [m34]; exact cw c hc
      have px : (K.tblPt (m + 1)).x = K.tbl + 8 * K.M.n * (3 * m + 0) := by
        rw [tblPt_x]; congr 2
      have py : (K.tblPt (m + 1)).y = K.tbl + 8 * K.M.n * (3 * m + 1) := by
        rw [tblPt_y, Nat.add_sub_cancel]
      have pz : (K.tblPt (m + 1)).z = K.tbl + 8 * K.M.n * (3 * m + 2) := by
        rw [tblPt_z, Nat.add_sub_cancel]
      have rx : K.R.x = K.R.x + 8 * K.M.n * 0 := by simp
      have ry : K.R.y = K.R.x + 8 * K.M.n * 1 := by rw [hL.rxy]; simp
      have rz : K.R.z = K.R.x + 8 * K.M.n * 2 := by rw [hL.rxz]; omega_arith
      have ex := ec 0 (by decide)
      have ey := ec 1 (by decide)
      have ez := ec 2 (by decide)
      rw [← px, ← rx] at ex
      rw [← py, ← ry] at ey
      rw [← pz, ← rz] at ez
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases mem3 hx with rfl | rfl | rfl
        · rw [ex]; exact lt₂ _ (by simp)
        · rw [ey]; exact lt₂ _ (by simp)
        · rw [ez]; exact lt₂ _ (by simp)
      · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [ex, ey, ez]
        exact r₂
  · intro x hx; rw [keepS x (oC x hx)]; exact lt₂ x hx
  · rw [tm _ (oC _ (by simp)), tm _ (oC _ (by simp)), tm _ (oC _ (by simp))]; exact d₂
  · rw [tm _ (oC _ (by simp)), tm _ (oC _ (by simp)), tm _ (oC _ (by simp))]; exact r₂
  · rw [tm _ (oC _ (by simp))]; exact z₂
  · rw [kt.gpr _ (by decide), a₄, x20₃]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
  · rw [x19t]; congr 1

/-- `R = P` into the first entry, `x20` at the second, seven to go. -/
theorem coZInit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    {P : Point C} {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkA K.M size C.p s₀.mem base) (hF : NafFixed K C base s₀ P k) :
    WP isa (.block (copyPt K.M.n K.R K.P ++ ([.addImm .x .x20 .x0 0] : List Instr) ++ store K ++
      ([.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0] : List Instr))) s₀ fun t =>
      Scr t base size ∧ KeepRegs (nafClob K.M.n) s₀ t ∧ Unch base (winW K) s₀.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧ OddTbl K C base P 1 t ∧
      t.gpr .x20 = off base (stride K * 1) ∧ t.gpr .x19 = BitVec.ofNat 64 7 := by
  have hW := hL.win
  have hn := hs.nowrap
  have a3 : RcbApart K.S ⟨K.zero, K.zero, K.zero⟩ K.P K.R :=
    hW.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 18, 18, 18, 19, 20, 21])
      rfl rfl
  have sP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K ++ winOther K := by
    intro x hx; apply List.mem_append_left
    rcases mem3 hx with rfl | rfl | rfl <;> simp [winRo]
  have sZ : ∀ x ∈ [K.zero, K.zero, K.zero], x ∈ winRo K ++ winOther K := by
    intro x hx; apply List.mem_append_left
    rcases mem3 hx with rfl | rfl | rfl <;> simp [winRo]
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  have sl₁ := winJ_sl (o := K.R) (p := ⟨K.zero, K.zero, K.zero⟩) (q := K.P) (R_other K) sZ sP
  have hRV : ∀ x ∈ rcbR K.S ⟨K.zero, K.zero, K.zero⟩ K.P, x ∈ winRo K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> simp [winRo]
  refine WP.mono (copyPointJ_ok hW.lay hL.al.al a3 sl₁.1 (inv_of hs hM (winRo_slots K) hF.ro_lt) hRV
    hF.pt) fun s₂ h₂ => ?_
  obtain ⟨sc₂, k₂, U₂, M₂, rlt₂, -, -, -⟩ := jacPost_frame hW hs hM (Or.inl rfl) h₂
  -- `x20 = base`.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok s₂ (d := .x20) (n := .x0) (imm := 0) (by decide)) fun s₃ ⟨a₃, k₃⟩ => ?_
  have sc₃ := sc₂.of_keeps k₃ (by decide)
  have x20₃ : s₃.gpr .x20 = off base (stride K * 0) := by
    rw [a₃, sc₂.x0]; simp [off]
  -- Entry 1.
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hL sc₃ (m := 0) (by decide) x20₃) fun s₄ ⟨cw, k₄, U₄⟩ => ?_
  have sc₄ := sc₃.of_keepRegs k₄ (by decide)
  rw [show ([.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0] : List Instr) =
    [.addImm .x .x20 .x20 (stride K)] ++ [.movz .x .x19 (BitVec.ofNat 16 7) 0] from rfl,
    WP.block_append_iff]
  have hst : stride K < 4096 := by have := hL.n6; simp only [stride]; omega_arith
  refine WP.mono (addImm_ok s₄ (d := .x20) (n := .x20) hst) fun s₅ ⟨a₅, k₅⟩ => ?_
  have sc₅ := sc₄.of_keeps k₅ (by decide)
  refine WP.mono (setCounter_ok s₅ (j := 7) (by decide)) fun t ⟨x19t, kt⟩ => ?_
  have sct := sc₅.of_keeps kt (by decide)
  have m4 : t.mem = s₄.mem := by rw [kt.mem, k₅.mem]
  have m3 : s₃.mem = s₂.mem := k₃.mem
  have hU4w : Unch base (winW K) s₂.mem t.mem := by
    rw [m4, ← m3]
    refine U₄.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, List.mem_append_right _ ?_, by rcases hw with rfl | rfl | rfl <;> rfl⟩
    obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := 0 + 1) (by omega_arith) (by omega_arith) w.1 (by
      rcases hw with rfl | rfl | rfl <;> simp)
    rw [e]; exact winTbl_mem K hi
  have kc : ∀ r ∈ [Reg.x20], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have kc4 : ∀ r ∈ [Reg.x4], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have kc19 : ∀ r ∈ [Reg.x19], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  refine ⟨sct, (k₂.mono clob_nafClob).trans ((Keeps.regs k₃).mono kc |>.trans
    ((k₄.mono kc4).trans ((Keeps.regs k₅).mono kc |>.trans ((Keeps.regs kt).mono kc19)))),
    (U₂.trans hU4w).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with hw | hw
      · exact loopW_sub K w hw
      · exact hw,
    M₂.unch hU4w (fun w hw => winW_mo hW M₂ w hw) hn, ?_, ?_, x19t⟩
  · intro a ha1 ha
    obtain rfl : a = 1 := by omega_arith
    have ec : ∀ c < 3, wordsVal t.mem base (K.tbl + 8 * K.M.n * (3 * 0 + c)) K.M.n =
        wordsVal s₂.mem base (K.R.x + 8 * K.M.n * c) K.M.n := fun c hc => by
      rw [m4, cw c hc, m3]
    have ex := ec 0 (by decide)
    have ey := ec 1 (by decide)
    have ez := ec 2 (by decide)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one] at ex ey ez
    rw [show K.tbl + 8 * K.M.n * 2 = (K.tblPt 1).z by simp [WinCfg.tblPt]; omega_arith,
      show K.R.x + 8 * K.M.n * 2 = K.R.z by rw [hL.rxz]; omega_arith] at ez
    rw [show K.tbl + 8 * K.M.n = (K.tblPt 1).y by simp [WinCfg.tblPt],
      show K.R.x + 8 * K.M.n = K.R.y by rw [hL.rxy]] at ey
    rw [show K.tbl = (K.tblPt 1).x by simp [WinCfg.tblPt]] at ex
    obtain ⟨-, -, -, -, -, rJ₂, -, -⟩ := jacPost_frame hW hs hM (Or.inl rfl) h₂
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases mem3 hx with rfl | rfl | rfl
      · rw [ex]; exact rlt₂ _ (by simp)
      · rw [ey]; exact rlt₂ _ (by simp)
      · rw [ez]; exact rlt₂ _ (by simp)
    · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [ex, ey, ez, show 2 * 1 - 1 = 1 from rfl, mul_one_pt]
      exact rJ₂
  · rw [kt.gpr _ (by decide), a₅, k₄.gpr _ (by decide), x20₃]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_zero, Nat.zero_add, Nat.mul_one]

/-- DBLU of the affine `P`: `E = 2P` and `R = P` at one `Z`. -/
theorem dbluStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {s₀ : State}
    (hF : NafFixed K C base s₀ P k) (hz1 : tmv C K.M.n base s₀ K.P.z = 1) {s : State}
    (hs : Scr s base size) (hk : KeepRegs (nafClob K.M.n) s₀ s) (hU : Unch base (winW K) s₀.mem s.mem)
    (hM : ModOkA K.M size C.p s.mem base) (hT : OddTbl K C base P 1 s)
    (h20 : s.gpr .x20 = off base (stride K * 1)) (h19 : s.gpr .x19 = BitVec.ofNat 64 7) :
    WP isa (fprogB K.M (dbluOps K)) s fun t =>
      CSt K C base size P s₀ t 1 ∧ t.gpr .x19 = BitVec.ofNat 64 (8 - 1) := by
  have hW := hL.win
  have hn := hs.nowrap
  have h10 : K.M.n < 10 := by have := hL.n6; omega_arith
  have ro : ∀ x ∈ winRo K, tmv C K.M.n base s x = tmv C K.M.n base s₀ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hW.ro_val hU hn hx]
  have hv : ∀ i ∈ [13, 14, 15], dbluσ K i ∈ winRo K := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [winRo, dbluσ]
  refine WP.mono (coZ_ok hL hp (dbluσ_ren hW) CoZTable.dblu_out CoZTable.dblu_reads
    (inv_of hs hM (winRo_slots K) (winRo_lt hW hF hU hn)) hv)
    fun t ⟨kt, Ut, It, et⟩ => ?_
  let e : Nat → Fe C := fun j => tmv C K.M.n base s (dbluσ K j)
  have e13 : e 13 = tmv C K.M.n base s₀ K.P.x := ro _ (hv 13 (by simp))
  have e14 : e 14 = tmv C K.M.n base s₀ K.P.y := ro _ (hv 14 (by simp))
  have e15 : e 15 = 1 := (ro _ (hv 15 (by simp))).trans hz1
  have hj : InvJ C (e 13) (e 14) 1 P := by rw [e13, e14, ← hz1]; exact hF.pt
  obtain ⟨jd, jr, jz⟩ := CoZTable.dblu_pts hC hO hn17 hM3 hP e15 hj
  have w : ∀ i ∈ [4, 5, 8, 9, 10], tmv C K.M.n base t (dbluσ K i) = runOps CoZ.dblu e i ∧
      wordsVal t.mem base (dbluσ K i) K.M.n < C.p := by
    intro i hi
    have hx : dbluσ K i ∈ (CoZ.dblu.map (FOp.rename (dbluσ K))).map FOp.out := out_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
    obtain ⟨v, l⟩ := written_val It hx
    exact ⟨v.trans (et i), l⟩
  obtain ⟨w4, l4⟩ := w 4 (by simp)
  obtain ⟨w5, l5⟩ := w 5 (by simp)
  obtain ⟨w8, l8⟩ := w 8 (by simp)
  obtain ⟨w9, l9⟩ := w 9 (by simp)
  obtain ⟨w10, l10⟩ := w 10 (by simp)
  have sct : Scr t base size := It.scr
  refine ⟨⟨sct, hk.trans (kt.mono clob_nafClob), ?_, It.mod, hT.unch hW (by omega_arith) Ut hn, ?_, ?_, ?_,
    ?_, ?_⟩, (kt.gpr _ (x19_not_clob _)).trans h19⟩
  · exact (hU.trans Ut).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [l8, l9, l5, l4, l10]
  · change InvJ C (tmv C K.M.n base t (dbluσ K 8)) (tmv C K.M.n base t (dbluσ K 9))
      (tmv C K.M.n base t (dbluσ K 10)) _
    rw [w8, w9, w10]; exact jd
  · change InvJ C (tmv C K.M.n base t (dbluσ K 5)) (tmv C K.M.n base t (dbluσ K 4))
      (tmv C K.M.n base t (dbluσ K 10)) _
    rw [w5, w4, w10, show 2 * 1 - 1 = 1 from rfl, mul_one_pt]; exact jr
  · change tmv C K.M.n base t (dbluσ K 10) ≠ 0
    rw [w10]; exact jz
  · exact (kt.gpr _ (x20_not_clob' h10)).trans h20

/-- The table: entries `1 … 8` hold `[1]P, [3]P, …, [15]P`. -/
theorem table_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkA K.M size C.p s₀.mem base) (hF : NafFixed K C base s₀ P k)
    (hz1 : tmv C K.M.n base s₀ K.P.z = 1) :
    WP isa (table K) s₀ fun t => NSt K C base size P s₀ t := by
  have hP0 : P ≠ .infinity := fun hh =>
    hC.one_ne_zero (hz1 ▸ (hF.pt.z_zero_iff hC).mpr hh)
  rw [table]
  refine WP.seq (WP.mono (coZInit_ok hL hs hM hF) fun s₁ ⟨sc₁, k₁, U₁, M₁, T₁, x20₁, x19₁⟩ => ?_)
  refine WP.seq (WP.mono (dbluStep_ok hL hp hC hM3 hO hn17 hP hF hz1 sc₁ k₁ U₁ M₁ T₁ x20₁ x19₁)
    fun s₂ ⟨T₂, x19₂⟩ => ?_)
  refine countLoop_ok (Inv := fun j t => CSt K C base size P s₀ t (8 - j) ∧ t.gpr .x19 = BitVec.ofNat 64 j)
    (n := 7) (by decide) (fun j t hj1 hj7 hI => ?_)
    (fun t hI => ⟨hI.1.scr, hI.1.keep, hI.1.unch, hI.1.mod, hI.1.tbl⟩) (by decide) ⟨by rw [show 8 - 7 = 1 from rfl]; exact T₂, x19₂⟩
  have e : 8 - (8 - j) = j := by omega_arith
  refine WP.mono (coZStep_ok hL hp hC hM3 hO hn17 hP hP0 hF (m := 8 - j) (by omega_arith) (by omega_arith) hI.1
    (by rw [e]; exact hI.2)) fun t' ⟨T', x'⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show 8 - (j - 1) = 8 - j + 1 by omega_arith]; exact T'
  · rw [x']; congr 1; omega_arith
  · rw [x']; congr 1; omega_arith

end VG.Proof.Weierstrass.AArch64.PubNaf
