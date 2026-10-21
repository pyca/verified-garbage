module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table2
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Framework.Omega

/-! # The window's entry of a run-time-width table

Slot 7 set to the table's entry named by the window word (`selectWindow_ok`),
by a scan of all sixteen entries under masks.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- Entry `j` lies within the table. -/
theorem te_le {len : Nat} {c : Ctx} {j : Nat} (hj : j < 16) :
    te len c 0 ≤ te len c j ∧ te len c j + bc len c ≤ te len c 16 := by
  have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega)
  rw [Nat.succ_mul] at this
  simp only [te]; omega

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx}

/-- `ebp` at entry `j`, `ebx` at slot 7, `edi` the bytes of a number. -/
theorem selPtrs_ok (h : In base bytes len args s) {j : Nat} (hj : j ≤ 16) {Q : State → Prop}
    (k : ∀ w, Keeps [.ebx, .edx, .ebp, .edi] s w → w.mem = s.mem → PtrAt w base .ebp (te len c j) →
      PtrAt w base .ebx (lo len (.slot c 7)) → (w.gpr .edi).toNat = 4 * cwc len c → Q w) :
    WP isa (.block (entryPtr c .ebp j .edx ++ ptrTo (.slot c 7) .ebx .edx ++ cntTo (one c) .edi)) s Q := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bl := h.bytes_lt
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  simp only [List.append_assoc]
  refine entryPtr_ok (c := c) (j := j) (r := .ebp) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    h.edi h.width h.upper' hj fun w₁ K₁ m₁ p₁ => ?_
  have h₁ := h.regs K₁ m₁
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot c 7) (by decide) (by decide) h₁.edi h₁.width h.upper'
    (by omega) fun w₂ K₂ m₂ p₂ => ?_
  have h₂ := h₁.regs K₂ m₂
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) h₂.width h.upper' (one_ok c).extra fun w₃ K₃ m₃ c₃ => WP.block_nil ?_
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  refine k w₃ (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
    (by rw [m₃, m₂, m₁]) ?_ ?_ ?_
  · rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
  · rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  · rw [cnt_toNat h.upper' (one_ok c) c₃, cw1]

/-- Entry `j` into slot 7 when the window word is `j`. -/
theorem selectEntry_ok (h : In base bytes len args s) (hw : w32 s.mem base winOff < 16) {j : Nat}
    (hj : j < 16) :
    WP isa (selectEntry c j) s fun u =>
      Outside base (lo len (.slot c 7)) (bc len c) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot c 7)) (cwc len c) =
        (if w32 s.mem base winOff = j then val32 s.mem base (te len c j) (cwc len c)
          else val32 s.mem base (lo len (.slot c 7)) (cwc len c)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
  unfold selectEntry
  rw [show ∀ a b c d : List Instr, a ++ b ++ c ++ d = a ++ (b ++ c ++ d) from by intros; simp]
  change WP isa (.seq (.block (VG.Impl.Mont.X86.Dynamic.windowMask j ++ _)) _) s _
  refine WP.seq (WP.block_append
    (WP.mono (VG.Proof.Mont.X86.Dynamic.windowMask_ok h.crt.scratch (by omega) (Nat.lt_trans hw (by decide)) (by omega)) fun w ⟨M, C, K⟩ => ?_))
  have h₁ := h.regs K M
  refine selPtrs_ok h₁ (j := j) (by omega) fun w₂ K₂ m₂ pe pb ce => ?_
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s w₂ := (K.mono (by decide)).trans (K₂.mono (by decide))
  have hk : w₂.gpr .ecx = cmask (decide (w32 s.mem base winOff = j)) := by
    rw [K₂.1 _ (by decide), C]
    show _ = cmask (decide (w32 s.mem base 4 = j))
    by_cases e : w32 s.mem base 4 = j <;> simp only [e, cmask, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  have mw : w₂.mem = s.mem := by rw [m₂, M]
  refine WP.mono (selectTail_ok h K₀ mw (x := te len c j) (d := lo len (.slot c 7)) (N := cwc len c)
    (k := decide (w32 s.mem base winOff = j)) (by omega) (by omega) (by omega) (by omega) pe pb ce hk)
    fun u ⟨O, V, _, Ku⟩ => ⟨?_, ?_, Ku⟩
  · rw [bw, ← mw]; exact O
  · rw [V, mw]; by_cases e : w32 s.mem base winOff = j <;> simp [e]

/-- Slot 7 keeps the window word and the table. -/
theorem slot7_keeps (h : In base bytes len args s) {m : Mem} (O : Outside base (lo len (.slot c 7)) (bc len c) s.mem m) :
    w32 m base winOff = w32 s.mem base winOff ∧
      ∀ j < 16, val32 m base (te len c j) (cwc len c) = val32 s.mem base (te len c j) (cwc len c) := by
  have nw := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have lo7 : numBase ≤ lo len (.slot c 7) := by simp [lo]
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  refine ⟨O.w32 (by simp only [winOff, numBase] at *; omega) (by simp only [winOff]; omega), fun j hj => ?_⟩
  obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
  exact O.val32 (.inr (by omega)) (by omega)

/-- Entries `1` to `k` into slot 7, each when the window word names it. -/
theorem selectEntries_ok (h : In base bytes len args s) (hw : w32 s.mem base winOff < 16) :
    ∀ k, k < 16 →
    WP isa (selectEntries c k) s fun u =>
      Outside base (lo len (.slot c 7)) (bc len c) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot c 7)) (cwc len c) =
        (if 0 < w32 s.mem base winOff ∧ w32 s.mem base winOff ≤ k then
          val32 s.mem base (te len c (w32 s.mem base winOff)) (cwc len c)
        else val32 s.mem base (lo len (.slot c 7)) (cwc len c)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, (ite_eq_right_iff.mpr fun h => absurd h (by omega)).symm,
      Keeps.refl _ _⟩
  | k + 1, hk => by
    have f8 := h.slot_fit c (j := 8) (by decide)
    have T := h.table_fit c
    have est : st len c = 2 * bc len c + 32 := rfl
    have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
    refine WP.seq (WP.mono (selectEntries_ok h hw k (by omega)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
    obtain ⟨win, tab⟩ := slot7_keeps h O₁
    refine WP.mono (selectEntry_ok h₁ (win ▸ hw) hk) fun u ⟨O₂, V₂, K₂⟩ => ⟨O₁.trans O₂, ?_, K₁.trans K₂⟩
    rw [V₂, win]
    by_cases e : w32 s.mem base winOff = k + 1
    · simp only [e, ↓reduceIte, Nat.zero_lt_succ, Nat.le_refl, and_self]
      exact tab _ hk
    · simp only [e, ↓reduceIte]
      rw [V₁]
      have e' : (0 < w32 s.mem base winOff ∧ w32 s.mem base winOff ≤ k + 1) ↔
          (0 < w32 s.mem base winOff ∧ w32 s.mem base winOff ≤ k) := by omega
      simp only [e']

/-- The window word's entry into slot 7. -/
theorem selectWindow_ok (h : In base bytes len args s) (hw : w32 s.mem base winOff < 16) :
    WP isa (selectWindow c) s fun u =>
      Outside base (lo len (.slot c 7)) (bc len c) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot c 7)) (cwc len c) =
        val32 s.mem base (te len c (w32 s.mem base winOff)) (cwc len c) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain ⟨_, t0'⟩ := te_le (len := len) (c := c) (j := 0) (by decide)
  unfold selectWindow
  simp only [List.cons_append]
  refine WP.seq (wp_movS rfl fun w₁ a₁ _ => ?_)
  have h₁ := h.regs a₁.keeps a₁.mem
  refine selPtrs_ok h₁ (j := 0) (by decide) fun w₂ K₂ m₂ pe pb ce => ?_
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s w₂ :=
    (a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))
  have mw : w₂.mem = s.mem := by rw [m₂, a₁.mem]
  refine WP.seq (WP.mono (selectTail_ok h K₀ mw (x := te len c 0) (d := lo len (.slot c 7)) (N := cwc len c)
    (k := true) (by omega) (by omega) (by omega) (by omega) pe pb ce (by rw [K₂.1 _ (by decide), a₁.gpr]; rfl))
    fun u₁ ⟨O₁, V₁, _, K₁⟩ => ?_)
  rw [mw, ← bw] at O₁
  rw [mw] at V₁
  have h₂ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  obtain ⟨win, tab⟩ := slot7_keeps h O₁
  refine WP.mono (selectEntries_ok h₂ (win ▸ hw) 15 (by decide)) fun u ⟨O₂, V₂, K₂⟩ =>
    ⟨O₁.trans O₂, ?_, K₁.trans K₂⟩
  rw [V₂, win]
  split
  · exact tab _ hw
  · rw [V₁]
    have : w32 s.mem base winOff = 0 := by omega
    rw [this]; rfl

end

end VG.Proof.Bignum.X86.CrtRt
