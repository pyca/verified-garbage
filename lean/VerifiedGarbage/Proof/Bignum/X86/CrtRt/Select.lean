module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table2
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem

/-! # The window's entry of a run-time-width table

Slot 7 set to the table's entry named by the window word (`selectWindow_ok`),
by a loop over all sixteen entries under masks (`selectStep_ok`), counting the
window word down from sixteen above the window back to it (`SelInv`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- Entry `j` lies within the table. -/
theorem te_le {len : Nat} {c : Ctx} {j : Nat} (hj : j < 16) :
    te len c 0 ≤ te len c j ∧ te len c j + bc len c ≤ te len c 16 := by
  have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega_arith)
  rw [Nat.succ_mul] at this
  simp only [te]; omega_arith

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx}

/-- `selectTail_ok` with `selectLoopX`, for at least four words. -/
theorem selectTailX_ok {s₀ : State} (h : In Ex base bytes len args s₀)
    (K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ s) (m₀ : s.mem = s₀.mem)
    {x d N : Nat} {k : Bool} (hN : 4 ≤ N) (hx : x + 4 * N ≤ bytes) (hd : d + 4 * N ≤ bytes)
    (hxd : d + 4 * N ≤ x ∨ x + 4 * N ≤ d) (pe : PtrAt s base .ebp x) (pb : PtrAt s base .ebx d)
    (ce : (s.gpr .edi).toNat = 4 * N) (hk : s.gpr .ecx = cmask k) :
    WP isa (.seq selectLoopX (.block restoreEdi)) s fun u =>
      Outside base d (4 * N) s.mem u.mem ∧
      val32 u.mem base d N = (if k then val32 s.mem base x N else val32 s.mem base d N) ∧
      PtrAt u base .ebx (d + 4 * N) ∧ PtrAt u base .ebp (x + 4 * N) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s₀ u := by
  have ws : Ws s base bytes := h.ws.of_keeps K₀
  have hn := h.scratch.nowrap
  refine WP.seq (WP.mono (selectLoopX_ok ws (x := x) (d := d) (N := N) k hN hx hd hxd pe pb ce hk)
    fun t ⟨O, V, pbt, pet, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ t := K₀.trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s₀.mem t.mem := by rw [← m₀]; exact O.mono (Nat.zero_le _) (by omega_arith)
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have ed : t₁.gpr .edi = s₀.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem]; exact O, by rw [u₁.mem]; exact V, by rw [PtrAt, u₁.other _ (by decide)]; exact pbt,
    by rw [PtrAt, u₁.other _ (by decide)]; exact pet, PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) ?_ ed⟩
  exact (Kall.trans (u₁.keeps.mono (by decide))).mono (by decide)

/-- A second 32-bit store at an address replaces the first. -/
theorem writeW32_twice (m : Mem) (a : Addr) (v v' : BitVec 32) :
    (m.writeW a v).writeW a v' = m.writeW a v' := by
  funext x
  simp only [Mem.writeW, Mem.write]
  split <;> rfl

/-- A 32-bit word stored back where it was read leaves the memory as it was. -/
theorem writeW32_w32 (m : Mem) (base : Addr) (o : Nat) :
    m.writeW (off base o) (BitVec.ofNat 32 (w32 m base o)) = m := by
  funext x
  simp only [Mem.writeW, Mem.write, w32, Mem.readW, BitVec.ofNat_toNat, Nat.reduceDiv, Nat.reduceMul,
    BitVec.setWidth_eq]
  split
  · rename_i hx
    rw [Mem.extractLsb'_read _ _ hx, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

/-- The same 32-bit store into two memories keeps what they share. -/
theorem Outside.writeW32 {base : Addr} {o n : Nat} {m m' : Mem} (O : Outside base o n m m') (a : Addr)
    (v : BitVec 32) : Outside base o n (m.writeW a v) (m'.writeW a v) := by
  intro x hx
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · exact O x hx

/-- The scan of the table at entry `j`: slot 7 the window's entry if the
window is below `j`, as it was otherwise; the window word sixteen above the
window less `j`, and the memory as it was but for slot 7 once the word is
back; `ebp` at entry `j`. -/
structure SelInv (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (c : Ctx) (s₀ : State) (j : Nat) (t : State) : Prop where
  inp : In Ex base bytes len args t
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s₀ t
  word : w32 t.mem base winOff = w32 s₀.mem base winOff + 16 - j
  out : Outside base (lo len (.slot c 7)) (bc len c) s₀.mem
    (t.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff)))
  val : val32 t.mem base (lo len (.slot c 7)) (cwc len c) =
    if w32 s₀.mem base winOff < j then val32 s₀.mem base (te len c (w32 s₀.mem base winOff)) (cwc len c)
    else val32 s₀.mem base (lo len (.slot c 7)) (cwc len c)
  ptr : PtrAt t base .ebp (te len c j)

/-- The window word's store leaves the numbers past the header. -/
theorem val32_writeWin (m : Mem) (base : Addr) (v : BitVec 32) {d N : Nat} (hd : numBase ≤ d)
    (hd' : d + 4 * N ≤ 2 ^ 64) :
    val32 (m.writeW (off base winOff) v) base d N = val32 m base d N :=
  (writeW32_outside m base v (by simp only [winOff]; omega_arith)).val32 (.inr (by simp only [winOff, numBase] at *; omega_arith))
    hd'

/-- One entry of the scan. -/
theorem selectStep_ok {s₀ t : State} (hw : w32 s₀.mem base winOff < 16) {j : Nat} (hj : j < 16)
    (I : SelInv Ex base bytes len args c s₀ j t) :
    WP isa (selectStep c) t fun u =>
      SelInv Ex base bytes len args c s₀ (j + 1) u ∧ u.zf = some (decide (j + 1 = 16)) := by
  obtain ⟨h, K, W, Ou, V, pe⟩ := I
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have est : st len c = 2 * bc len c + 32 := rfl
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have lo7 : numBase ≤ lo len (.slot c 7) := by simp [lo]
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have tsucc : ∀ i, te len c (i + 1) = te len c i + bc len c := fun i => by
    simp only [te]; rw [Nat.succ_mul]; omega_arith
  have t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega_arith
  obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
  have T8 : lo len (.slot c 8) + st len c ≤ te len c 0 := by rw [t0]; exact T.1
  unfold selectStep
  simp only [List.append_assoc]
  -- The mask.
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.windowMask_ok h.scratch (by omega_arith)
    (show w32 t.mem base winOff < 32 by omega_arith) (by decide)) fun w₁ ⟨m₁, C₁, K₁⟩ => ?_))
  have h₁ := h.regs K₁ m₁
  -- The window word down one.
  refine wp_movS (readSrc_sc h₁.scratch (d := winOff) (by omega_arith)) fun w₂ a₂ _ => ?_
  refine wp_subS rfl fun w₃ a₃ _ => ?_
  have K₃ : Keeps [.eax, .ecx] t w₃ := (K₁.trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))
  have m₃ : w₃.mem = t.mem := by rw [a₃.mem, a₂.mem, m₁]
  have h₃ := h.regs K₃ m₃
  refine wp_storeS (h₃.scratch.ea (d := winOff) (by omega_arith))
    (h₃.scratch.write (d := winOff) (by omega_arith)) fun w₄ s₄ => ?_
  have v₃ : w₃.gpr .eax = BitVec.ofNat 32 (w32 s₀.mem base winOff + 16 - (j + 1)) := by
    rw [a₃.gpr, a₂.gpr, m₁]
    apply BitVec.eq_of_toNat_eq
    have W' : (t.mem.readW (off base winOff) 32).toNat = w32 s₀.mem base winOff + 16 - j := W
    have one : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, W', one, BitVec.toNat_ofNat]
    omega_arith
  have m₄ : w₄.mem = t.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff + 16 - (j + 1))) := by
    rw [s₄.mem, m₃, v₃]
  have K₄ : Keeps [.eax, .ecx] t w₄ := K₃.trans (s₄.keeps _)
  have O₄ : Outside base 0 bytes t.mem w₄.mem := by
    rw [m₄]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.zero_le _) (by omega_arith)
  have h₄ := h.keep K₄ (by decide) (by decide) O₄
  -- The pointers.
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot c 7) (by decide) (by decide) h₄.edi h₄.width h.upper'
    (by omega_arith) fun w₅ K₅ m₅ p₅ => ?_
  have h₅ := h₄.regs K₅ m₅
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) h₅.width h.upper' (one_ok c).extra fun w₆ K₆ m₆ c₆ => WP.block_nil ?_
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] w₄ w₆ := (K₅.mono (by decide)).trans (K₆.mono (by decide))
  have mw : w₆.mem = w₄.mem := by rw [m₆, m₅]
  have k₆ : w₆.gpr .ecx = cmask (decide (w32 s₀.mem base winOff = j)) := by
    rw [K₆.1 _ (by decide), K₅.1 _ (by decide), s₄.gpr, a₃.other _ (by decide), a₂.other _ (by decide), C₁]
    show (if w32 t.mem base winOff = 16 then _ else _) = _
    rw [W]
    by_cases e : w32 s₀.mem base winOff = j
    · simp only [e, cmask, decide_true, ↓reduceIte, show j + 16 - j = 16 by omega_arith]
    · simp only [e, cmask, decide_false, Bool.false_eq_true, ↓reduceIte,
        show ¬(w32 s₀.mem base winOff + 16 - j = 16) by omega_arith]
  have pe₆ : PtrAt w₆ base .ebp (te len c j) := by
    rw [PtrAt, K₆.1 _ (by decide), K₅.1 _ (by decide), s₄.gpr, a₃.other _ (by decide), a₂.other _ (by decide),
      K₁.1 _ (by decide)]; exact pe
  have pb₆ : PtrAt w₆ base .ebx (lo len (.slot c 7)) := by rw [PtrAt, K₆.1 _ (by decide)]; exact p₅
  -- The selection.
  refine WP.seq (WP.mono (selectTailX_ok h₄ K₀ mw (x := te len c j) (d := lo len (.slot c 7)) (N := cwc len c)
    (k := decide (w32 s₀.mem base winOff = j)) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) pe₆ pb₆ (by rw [cnt_toNat h.upper' (one_ok c) c₆, cw1]) k₆)
    fun u₁ ⟨O₇, V₇, _, pe₇, K₇⟩ => ?_)
  rw [mw, ← bw] at O₇
  rw [mw] at V₇
  have h₇ := h₄.keep K₇ (by decide) (by decide) (O₇.mono (Nat.zero_le _) (by omega_arith))
  -- The end of the table.
  refine entryPtr_ok (c := c) (j := 16) (r := .edx) (t := .eax) (by decide) (by decide) (by decide) (by decide)
    h₇.edi h₇.width h.upper' (by decide) fun v₂ K₈ m₈ p₈ => wp_cmpS rfl fun v₃ f₃ z₃ => WP.block_nil ?_
  have pe₈ : PtrAt v₂ base .ebp (te len c (j + 1)) := by
    rw [PtrAt, K₈.1 _ (by decide), tsucc, bw]; exact pe₇
  have m₉ : v₃.mem = u₁.mem := by rw [f₃.mem, m₈]
  have K₉ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] t v₃ :=
    (((K₄.mono (by decide)).trans K₇).trans (K₈.mono (by decide))).trans (f₃.keeps _)
  have h₉ := h₇.regs ((K₈.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp] u₁ v₂).trans (f₃.keeps _))
    (by rw [f₃.mem, m₈])
  -- The word, the memory and slot 7.
  have W₉ : w32 v₃.mem base winOff = w32 s₀.mem base winOff + 16 - (j + 1) := by
    rw [m₉, O₇.w32 (.inl (by omega_arith)) (by omega_arith), m₄, w32_write_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)]
  have Ou₉ : Outside base (lo len (.slot c 7)) (bc len c) s₀.mem
      (v₃.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff))) := by
    refine Ou.trans ?_
    have e : t.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff)) =
        w₄.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff)) := by
      rw [m₄, writeW32_twice]
    rw [e, m₉]
    exact Outside.writeW32 O₇ _ _
  have Vt : ∀ d, numBase ≤ d → d + 4 * cwc len c ≤ bytes →
      (d + 4 * cwc len c ≤ lo len (.slot c 7) ∨ lo len (.slot c 7) + bc len c ≤ d) →
      val32 t.mem base d (cwc len c) = val32 s₀.mem base d (cwc len c) := fun d hd hb hs => by
    rw [← Ou.val32 hs (by omega_arith), val32_writeWin _ _ _ hd (by omega_arith)]
  refine ⟨⟨h₉, K.trans K₉, W₉, Ou₉, ?_, by rw [PtrAt, f₃.gpr]; exact pe₈⟩, ?_⟩
  · rw [m₉, V₇, m₄, val32_writeWin _ _ _ (by omega_arith) (by omega_arith),
      val32_writeWin _ _ _ (by omega_arith) (by omega_arith)]
    by_cases e : w32 s₀.mem base winOff = j
    · simp only [e, decide_true, ↓reduceIte, show j < j + 1 by omega_arith]
      exact Vt _ (by omega_arith) (by omega_arith) (.inr (by omega_arith))
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [V]
      have e' : (w32 s₀.mem base winOff < j + 1) ↔ (w32 s₀.mem base winOff < j) := by omega_arith
      simp only [e']
  · have tj1 := tsucc j
    rw [z₃, ptr_beq pe₈ p₈ (by omega_arith) (by omega_arith)]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e
      have e' : (j + 1) * bc len c = 16 * bc len c := by simp only [te] at e; omega_arith
      exact Nat.eq_of_mul_eq_mul_right (by omega_arith) e'
    · intro e; rw [e]

/-- The window word's entry into slot 7. -/
theorem selectWindow_ok (h : In Ex base bytes len args s) (hw : w32 s.mem base winOff < 16) :
    WP isa (selectWindow c) s fun u =>
      Outside base (lo len (.slot c 7)) (bc len c) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot c 7)) (cwc len c) =
        val32 s.mem base (te len c (w32 s.mem base winOff)) (cwc len c) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bl := h.bytes_lt
  have lo7 : numBase ≤ lo len (.slot c 7) := by simp [lo]
  have est : st len c = 2 * bc len c + 32 := rfl
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have bw := bc_eq_cwc len c
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  unfold selectWindow
  simp only [List.cons_append]
  -- The window word up sixteen.
  refine WP.seq (wp_movS (readSrc_sc h.scratch (d := winOff) (by omega_arith)) fun w₁ a₁ _ => ?_)
  refine wp_addS rfl fun w₂ a₂ _ => ?_
  have K₂ : Keeps [.eax] s w₂ := (a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))
  have h₂ := h.regs K₂ (by rw [a₂.mem, a₁.mem])
  refine wp_storeS (h₂.scratch.ea (d := winOff) (by omega_arith))
    (h₂.scratch.write (d := winOff) (by omega_arith)) fun w₃ s₃ => ?_
  have v₂ : w₂.gpr .eax = BitVec.ofNat 32 (w32 s.mem base winOff + 16 - 0) := by
    rw [a₂.gpr, a₁.gpr]
    apply BitVec.eq_of_toNat_eq
    have W' : (s.mem.readW (off base winOff) 32).toNat = w32 s.mem base winOff := rfl
    have sixteen : (16 : BitVec 32).toNat = 16 := rfl
    rw [BitVec.toNat_add, W', sixteen, BitVec.toNat_ofNat]
    omega_arith
  have m₃ : w₃.mem = s.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s.mem base winOff + 16 - 0)) := by
    rw [s₃.mem, a₂.mem, a₁.mem, v₂]
  have K₃ : Keeps [.eax] s w₃ := K₂.trans (s₃.keeps _)
  have h₃ := h.keep K₃ (by decide) (by decide)
    (by rw [m₃]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.zero_le _) (by omega_arith))
  -- The table's first entry.
  rw [← List.append_nil (entryPtr c .ebp 0 .edx)]
  refine entryPtr_ok (c := c) (j := 0) (r := .ebp) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    h₃.edi h₃.width h.upper' (by decide) fun w₄ K₄ m₄ p₄ => WP.block_nil ?_
  have I₀ : SelInv Ex base bytes len args c s 0 w₄ := by
    refine ⟨h₃.regs K₄ m₄, (K₃.mono (by decide)).trans (K₄.mono (by decide)), ?_, ?_, ?_, p₄⟩
    · rw [m₄, m₃, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [m₄, m₃, writeW32_twice, writeW32_w32]; exact Outside.refl _ _ _ _
    · simp only [Nat.not_lt_zero, ↓reduceIte]
      rw [m₄, m₃, val32_writeWin _ _ _ lo7 (by omega_arith)]
  -- The scan.
  refine WP.mono (PublicRt.countLoop (N := 16) (by decide) (fun j t => SelInv Ex base bytes len args c s j t)
    (fun j t hj I => selectStep_ok hw hj I) I₀) fun u ⟨_, Ku, Wu, Ou, Vu, _⟩ => ⟨?_, ?_, Ku⟩
  · have e : u.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s.mem base winOff)) = u.mem := by
      rw [show w32 s.mem base winOff = w32 u.mem base winOff by omega_arith, writeW32_w32]
    rw [e] at Ou; exact Ou
  · rw [Vu]; simp only [hw, ↓reduceIte]

end

end VG.Proof.Bignum.X86.CrtRt
