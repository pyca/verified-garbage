module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.RepeatSquares
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table2
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Mont.X86.WindowWords
import VerifiedGarbage.Proof.Mont.X86.PowerInit

/-! ### `Bignum.X86.CrtRt.WindowPower`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.CrtRt.Window`, which only this module used -/

section

/-! ### `Bignum.X86.CrtRt.Select`, which only this module used -/

section

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
  obtain ws : Ws s base bytes := h.ws.of_keeps K₀
  have hn := h.scratch.nowrap
  refine WP.seq (WP.mono (selectLoopX_ok ws (x := x) (d := d) (N := N) k hN hx hd hxd pe pb ce hk)
    fun t ⟨O, V, pbt, pet, Kt⟩ => ?_)
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ t := K₀.trans (Kt.mono (by decide))
  obtain Oall : Outside base 0 bytes s₀.mem t.mem := by rw [← m₀]; exact O.mono (Nat.zero_le _) (by omega_arith)
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  obtain ed : t₁.gpr .edi = s₀.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
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
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain lo7 : numBase ≤ lo len (.slot c 7) := by simp [lo]
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain tsucc : ∀ i, te len c (i + 1) = te len c i + bc len c := fun i => by
    simp only [te]; rw [Nat.succ_mul]; omega_arith
  obtain t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega_arith
  obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
  obtain T8 : lo len (.slot c 8) + st len c ≤ te len c 0 := by rw [t0]; exact T.1
  unfold selectStep
  simp only [List.append_assoc]
  -- The mask.
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.windowMask_ok h.scratch (by omega_arith)
    (show w32 t.mem base winOff < 32 by omega_arith) (by decide)) fun w₁ ⟨m₁, C₁, K₁⟩ => ?_))
  obtain h₁ := h.regs K₁ m₁
  -- The window word down one.
  refine wp_movS (readSrc_sc h₁.scratch (d := winOff) (by omega_arith)) fun w₂ a₂ _ => ?_
  refine wp_subS rfl fun w₃ a₃ _ => ?_
  obtain K₃ : Keeps [.eax, .ecx] t w₃ := (K₁.trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))
  obtain m₃ : w₃.mem = t.mem := by rw [a₃.mem, a₂.mem, m₁]
  obtain h₃ := h.regs K₃ m₃
  refine wp_storeS (h₃.scratch.ea (d := winOff) (by omega_arith))
    (h₃.scratch.write (d := winOff) (by omega_arith)) fun w₄ s₄ => ?_
  obtain v₃ : w₃.gpr .eax = BitVec.ofNat 32 (w32 s₀.mem base winOff + 16 - (j + 1)) := by
    rw [a₃.gpr, a₂.gpr, m₁]
    apply BitVec.eq_of_toNat_eq
    have W' : (t.mem.readW (off base winOff) 32).toNat = w32 s₀.mem base winOff + 16 - j := W
    have one : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, W', one, BitVec.toNat_ofNat]
    omega_arith
  obtain m₄ : w₄.mem = t.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff + 16 - (j + 1))) := by
    rw [s₄.mem, m₃, v₃]
  obtain K₄ : Keeps [.eax, .ecx] t w₄ := K₃.trans (s₄.keeps _)
  obtain O₄ : Outside base 0 bytes t.mem w₄.mem := by
    rw [m₄]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.zero_le _) (by omega_arith)
  obtain h₄ := h.keep K₄ (by decide) (by decide) O₄
  -- The pointers.
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot c 7) (by decide) (by decide) h₄.edi h₄.width h.upper'
    (by omega_arith) fun w₅ K₅ m₅ p₅ => ?_
  obtain h₅ := h₄.regs K₅ m₅
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) h₅.width h.upper' (one_ok c).extra fun w₆ K₆ m₆ c₆ => WP.block_nil ?_
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] w₄ w₆ := (K₅.mono (by decide)).trans (K₆.mono (by decide))
  obtain mw : w₆.mem = w₄.mem := by rw [m₆, m₅]
  obtain k₆ : w₆.gpr .ecx = cmask (decide (w32 s₀.mem base winOff = j)) := by
    rw [K₆.1 _ (by decide), K₅.1 _ (by decide), s₄.gpr, a₃.other _ (by decide), a₂.other _ (by decide), C₁]
    show (if w32 t.mem base winOff = 16 then _ else _) = _
    rw [W]
    by_cases e : w32 s₀.mem base winOff = j
    · simp only [e, cmask, decide_true, ↓reduceIte, show j + 16 - j = 16 by omega_arith]
    · simp only [e, cmask, decide_false, Bool.false_eq_true, ↓reduceIte,
        show ¬(w32 s₀.mem base winOff + 16 - j = 16) by omega_arith]
  obtain pe₆ : PtrAt w₆ base .ebp (te len c j) := by
    rw [PtrAt, K₆.1 _ (by decide), K₅.1 _ (by decide), s₄.gpr, a₃.other _ (by decide), a₂.other _ (by decide),
      K₁.1 _ (by decide)]; exact pe
  obtain pb₆ : PtrAt w₆ base .ebx (lo len (.slot c 7)) := by rw [PtrAt, K₆.1 _ (by decide)]; exact p₅
  -- The selection.
  refine WP.seq (WP.mono (selectTailX_ok h₄ K₀ mw (x := te len c j) (d := lo len (.slot c 7)) (N := cwc len c)
    (k := decide (w32 s₀.mem base winOff = j)) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) pe₆ pb₆ (by rw [cnt_toNat h.upper' (one_ok c) c₆, cw1]) k₆)
    fun u₁ ⟨O₇, V₇, _, pe₇, K₇⟩ => ?_)
  rw [mw, ← bw] at O₇
  rw [mw] at V₇
  obtain h₇ := h₄.keep K₇ (by decide) (by decide) (O₇.mono (Nat.zero_le _) (by omega_arith))
  -- The end of the table.
  refine entryPtr_ok (c := c) (j := 16) (r := .edx) (t := .eax) (by decide) (by decide) (by decide) (by decide)
    h₇.edi h₇.width h.upper' (by decide) fun v₂ K₈ m₈ p₈ => wp_cmpS rfl fun v₃ f₃ z₃ => WP.block_nil ?_
  obtain pe₈ : PtrAt v₂ base .ebp (te len c (j + 1)) := by
    rw [PtrAt, K₈.1 _ (by decide), tsucc, bw]; exact pe₇
  obtain m₉ : v₃.mem = u₁.mem := by rw [f₃.mem, m₈]
  obtain K₉ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] t v₃ :=
    (((K₄.mono (by decide)).trans K₇).trans (K₈.mono (by decide))).trans (f₃.keeps _)
  obtain h₉ := h₇.regs ((K₈.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp] u₁ v₂).trans (f₃.keeps _))
    (by rw [f₃.mem, m₈])
  -- The word, the memory and slot 7.
  obtain W₉ : w32 v₃.mem base winOff = w32 s₀.mem base winOff + 16 - (j + 1) := by
    rw [m₉, O₇.w32 (.inl (by omega_arith)) (by omega_arith), m₄, w32_write_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)]
  obtain Ou₉ : Outside base (lo len (.slot c 7)) (bc len c) s₀.mem
      (v₃.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff))) := by
    refine Ou.trans ?_
    obtain e : t.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff)) =
        w₄.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s₀.mem base winOff)) := by
      rw [m₄, writeW32_twice]
    rw [e, m₉]
    exact Outside.writeW32 O₇ _ _
  obtain Vt : ∀ d, numBase ≤ d → d + 4 * cwc len c ≤ bytes →
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
      obtain e' : (w32 s₀.mem base winOff < j + 1) ↔ (w32 s₀.mem base winOff < j) := by omega_arith
      simp only [e']
  · have tj1 := tsucc j
    rw [z₃, ptr_beq pe₈ p₈ (by omega_arith) (by omega_arith)]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e
      obtain e' : (j + 1) * bc len c = 16 * bc len c := by simp only [te] at e; omega_arith
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
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  have bl := h.bytes_lt
  obtain lo7 : numBase ≤ lo len (.slot c 7) := by simp [lo]
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain bw := bc_eq_cwc len c
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  unfold selectWindow
  simp only [List.cons_append]
  -- The window word up sixteen.
  refine WP.seq (wp_movS (readSrc_sc h.scratch (d := winOff) (by omega_arith)) fun w₁ a₁ _ => ?_)
  refine wp_addS rfl fun w₂ a₂ _ => ?_
  obtain K₂ : Keeps [.eax] s w₂ := (a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))
  obtain h₂ := h.regs K₂ (by rw [a₂.mem, a₁.mem])
  refine wp_storeS (h₂.scratch.ea (d := winOff) (by omega_arith))
    (h₂.scratch.write (d := winOff) (by omega_arith)) fun w₃ s₃ => ?_
  obtain v₂ : w₂.gpr .eax = BitVec.ofNat 32 (w32 s.mem base winOff + 16 - 0) := by
    rw [a₂.gpr, a₁.gpr]
    apply BitVec.eq_of_toNat_eq
    have W' : (s.mem.readW (off base winOff) 32).toNat = w32 s.mem base winOff := rfl
    have sixteen : (16 : BitVec 32).toNat = 16 := rfl
    rw [BitVec.toNat_add, W', sixteen, BitVec.toNat_ofNat]
    omega_arith
  obtain m₃ : w₃.mem = s.mem.writeW (off base winOff) (BitVec.ofNat 32 (w32 s.mem base winOff + 16 - 0)) := by
    rw [s₃.mem, a₂.mem, a₁.mem, v₂]
  obtain K₃ : Keeps [.eax] s w₃ := K₂.trans (s₃.keeps _)
  obtain h₃ := h.keep K₃ (by decide) (by decide)
    (by rw [m₃]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.zero_le _) (by omega_arith))
  -- The table's first entry.
  rw [← List.append_nil (entryPtr c .ebp 0 .edx)]
  refine entryPtr_ok (c := c) (j := 0) (r := .ebp) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    h₃.edi h₃.width h.upper' (by decide) fun w₄ K₄ m₄ p₄ => WP.block_nil ?_
  obtain I₀ : SelInv Ex base bytes len args c s 0 w₄ := by
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

end

end


/-! # A window of a run-time-width exponentiation

Four squares of slot 6, the window's entry into slot 7, and their product
(`windowStep_ok`), keeping the context, slot 3 and the table.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges a window changes. -/
abbrev wR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(winOff, 4), (lo len (.slot c 1), 3 * bc len c + 56), (lo len (.slot c 6), bc len c),
    (lo len (.slot c 7), bc len c), (lo len (.slot c 8), bc len c)]

/-- The ranges of `nextWindow`. -/
abbrev nwR (len : Nat) (c : Ctx) : List (Nat × Nat) := [(winOff, 4), (lo len (.slot c 8), bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

theorem wR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ wR len c, p.1 + p.2 ≤ bytes := by
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  intro p hp
  simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem wR_hdr (len : Nat) (c : Ctx) :
    ∀ p ∈ wR len c, numBase + bc len c ≤ p.1 ∨ (4 ≤ p.1 ∧ p.1 + p.2 ≤ numBase) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  intro p hp
  simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem wR_sub_nw (len : Nat) (c : Ctx) : ∀ p ∈ nwR len c, p ∈ wR len c := by
  intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp

theorem wR_sub_mul (len : Nat) (c : Ctx) : ∀ p ∈ mulR len c 6, p ∈ wR len c := by
  intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp

/-- A window keeps slot 3 and the table. -/
theorem wR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (wR len c)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 3 = sv m base len c 3 ∧
      ∀ j < 16, val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e3 : lo len (.slot c 3) = numBase + 3 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain fit := wR_fit h c
  refine ⟨frameR_val32 F R nw (by omega_arith) ?_ fit, fun j hj => ?_⟩
  · intro p hp; simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    refine frameR_val32 F R nw (by omega_arith) ?_ fit
    intro p hp; simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- A product into slot 6 keeps slot 8 and the table. -/
theorem mulR6_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (mulR len c 6)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 8 = sv m base len c 8 ∧
      ∀ j < 16, val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain fit : ∀ p ∈ mulR len c 6, p.1 + p.2 ≤ bytes := fun p hp => wR_fit h c p (wR_sub_mul len c p hp)
  refine ⟨frameR_val32 F R nw (by omega_arith) ?_ fit, fun j hj => ?_⟩
  · intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    refine frameR_val32 F R nw (by omega_arith) ?_ fit
    intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith

/-- The window's shift keeps slot 6 and the table. -/
theorem nwR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (nwR len c)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 6 = sv m base len c 6 ∧
      ∀ j < 16, val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain fit : ∀ p ∈ nwR len c, p.1 + p.2 ≤ bytes := fun p hp => wR_fit h c p (wR_sub_nw len c p hp)
  refine ⟨frameR_val32 F R nw (by omega_arith) ?_ fit, fun j hj => ?_⟩
  · intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    refine frameR_val32 F R nw (by omega_arith) ?_ fit
    intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith

/-- A square of slot 6. -/
theorem square_ok (C : CtxOk Ex base bytes len args c M s) {y : Nat}
    (hy : sv s.mem base len c 6 = y * 2 ^ (8 * bc len c) % M) :
    WP isa (square c) s fun t => CtxOk Ex base bytes len args c M t ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame (frameR base (s.gpr .esp) (mulR len c 6)) s.mem t.mem ∧
      sv t.mem base len c 6 = y ^ 2 * 2 ^ (8 * bc len c) % M := by
  have hM := C.gt
  unfold square
  refine WP.mono (cmul_ok C (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hy]; exact Nat.mod_lt _ (by omega_arith))) fun t ⟨C', K, F, L, V⟩ => ⟨C', K, F, ?_⟩
  obtain v := VG.Proof.Dsa.mont_product C.coprime (a := y) (b := y) (by rw [hy, Nat.mod_mod])
    (by rw [hy, Nat.mod_mod]) V
  rw [Nat.mod_eq_of_lt L] at v
  rw [v, Nat.pow_two]

/-- Four squares of slot 6, then `P`. -/
theorem squares_ok (C : CtxOk Ex base bytes len args c M s) {y : Nat}
    (hy : sv s.mem base len c 6 = y * 2 ^ (8 * bc len c) % M) {P : Prog isa} {Q : State → Prop}
    (k : ∀ t, CtxOk Ex base bytes len args c M t → Keeps [.eax, .ecx, .edx] s t →
      Frame (frameR base (s.gpr .esp) (mulR len c 6)) s.mem t.mem →
      sv t.mem base len c 6 = y ^ 16 * 2 ^ (8 * bc len c) % M → WP isa P t Q) :
    WP isa (.seq (square c) (.seq (square c) (.seq (square c) (.seq (square c) P)))) s Q := by
  refine WP.seq (WP.mono (square_ok C hy) fun t₁ ⟨C₁, K₁, F₁, V₁⟩ => ?_)
  refine WP.seq (WP.mono (square_ok C₁ V₁) fun t₂ ⟨C₂, K₂, F₂, V₂⟩ => ?_)
  refine WP.seq (WP.mono (square_ok C₂ V₂) fun t₃ ⟨C₃, K₃, F₃, V₃⟩ => ?_)
  refine WP.seq (WP.mono (square_ok C₃ V₃) fun t₄ ⟨C₄, K₄, F₄, V₄⟩ => ?_)
  obtain sp₁ : t₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  obtain sp₂ : t₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  obtain sp₃ : t₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  rw [sp₁] at F₂
  rw [sp₂] at F₃
  rw [sp₃] at F₄
  refine k t₄ C₄ (((K₁.trans K₂).trans K₃).trans K₄) (((F₁.trans F₂).trans F₃).trans F₄) ?_
  rw [V₄, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]

/-- A window: slot 6 to `y^16 b^w` (in Montgomery form) for the top four bits `w` of slot 8, slot 8
shifted up past them, and `esi` down one. -/
theorem windowStep_ok (C : CtxOk Ex base bytes len args c M s) {b y n : Nat}
    (hT : ∀ j < 16, val32 s.mem base (te len c j) (cwc len c) = b ^ j * 2 ^ (8 * bc len c) % M)
    (hy : sv s.mem base len c 6 = y * 2 ^ (8 * bc len c) % M) (hn0 : 0 < n) (hn : n < 2 ^ 32)
    (he : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (windowStep c) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (wR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      u.gpr .esi = BitVec.ofNat 32 (n - 1) ∧ u.zf = some (decide (n = 1)) ∧
      sv u.mem base len c 6 =
        y ^ 16 * b ^ (sv s.mem base len c 8 * 16 / 2 ^ (32 * cwc len c)) * 2 ^ (8 * bc len c) % M ∧
      sv u.mem base len c 8 = sv s.mem base len c 8 * 16 % 2 ^ (32 * cwc len c) := by
  have h := C.inp
  have hM := C.gt
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have nw := h.scratch.nowrap
  obtain fitW := wR_fit h c
  obtain hdrW := wR_hdr len c
  unfold windowStep
  refine squares_ok C hy fun t₁ C₁ K₁ F₁ V₁ => ?_
  obtain ⟨E₁, T₁⟩ := mulR6_keep h F₁ h.room
  obtain sp₁ : t₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- The window.
  refine WP.seq (WP.mono (nextWindow_ok C₁.inp c) fun t₂ ⟨F₂, W₂, E₂, K₂⟩ => ?_)
  obtain ⟨Y₂, T₂⟩ := nwR_keep C₁.inp F₂ C₁.inp.room
  obtain C₂ := C₁.keepF2 K₂ (by decide) (by decide) F₂ (fun p hp => fitW p (wR_sub_nw len c p hp))
    (fun p hp => hdrW p (wR_sub_nw len c p hp))
  obtain sp₂ : t₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  obtain hw : w32 t₂.mem base winOff < 16 := by
    rw [W₂, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have := val32_lt t₁.mem base (lo len (.slot c 8)) (cwc len c)
    simp only [sv]; omega_arith
  -- Its entry.
  refine WP.seq (WP.mono (selectWindow_ok C₂.inp hw) fun t₃ ⟨O₃, S₃, K₃⟩ => ?_)
  obtain F₃ : Frame (frameR base (t₂.gpr .esp) (wR len c)) t₂.mem t₃.mem :=
    frameR_of_outside O₃ (by omega_arith) (by simp)
  obtain C₃ := C₂.keepF2 K₃ (by decide) (by decide) F₃ fitW hdrW
  obtain sp₃ : t₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  obtain S₃' : sv t₃.mem base len c 7 = b ^ w32 t₂.mem base winOff * 2 ^ (8 * bc len c) % M := by
    simp only [sv]; rw [S₃, T₂ _ hw, T₁ _ hw, hT _ hw]
  obtain Y₃ : sv t₃.mem base len c 6 = y ^ 16 * 2 ^ (8 * bc len c) % M := by
    simp only [sv]; rw [O₃.val32 (.inl (by omega_arith)) (by omega_arith)]; simp only [sv] at Y₂ V₁; rw [Y₂, V₁]
  obtain E₃ : sv t₃.mem base len c 8 = sv t₂.mem base len c 8 := by
    simp only [sv]; rw [O₃.val32 (.inr (by omega_arith)) (by omega_arith)]
  -- The product.
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [S₃']; exact Nat.mod_lt _ (by omega_arith))) fun t₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  obtain ⟨E₄, _⟩ := mulR6_keep C₃.inp F₄ C₃.inp.room
  obtain sp₄ : t₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  -- The count.
  obtain Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t₄ :=
    (((K₁.mono (by decide)).trans K₂).trans K₃).trans (K₄.mono (by decide))
  obtain esi₄ : t₄.gpr .esi = BitVec.ofNat 32 n := (Kt.1 _ (by decide)).trans he
  refine wp_subZ rfl fun u a₅ z₅ => WP.block_nil ?_
  obtain sub : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) :=
    VG.Proof.Mont.X86.Dynamic.counter_sub hn hn0
  refine ⟨C₄.regs a₅.keeps a₅.mem, ?_, (Kt.mono (by decide)).trans (a₅.keeps.mono (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [a₅.mem]
    rw [sp₁] at F₂
    rw [sp₂] at F₃
    rw [sp₃] at F₄
    exact (((frameR_mono F₁ (wR_sub_mul len c)).trans (frameR_mono F₂ (wR_sub_nw len c))).trans F₃).trans
      (frameR_mono F₄ (wR_sub_mul len c))
  · rw [a₅.gpr, esi₄, sub]
  · rw [z₅, esi₄, sub]
    obtain z := VG.Proof.Mont.X86.Dynamic.counter_zero hn hn0
    rw [show ∀ x : BitVec 32, x - 0 = x from BitVec.sub_zero] at z
    rw [z]
  · rw [sv, a₅.mem]
    obtain v := VG.Proof.Dsa.mont_product C₃.coprime (a := y ^ 16) (b := b ^ w32 t₂.mem base winOff)
      (by rw [Y₃, Nat.mod_mod]) (by rw [S₃', Nat.mod_mod]) V₄
    rw [Nat.mod_eq_of_lt L₄, W₂, E₁] at v
    exact v
  · rw [sv, a₅.mem]; simp only [sv] at E₄ E₃ E₂ E₁ ⊢; rw [E₄, E₃, E₂, E₁]

end

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # A run-time-width exponentiation by fixed windows

`windowPower_ok`: slot 6 set to slot 5 to the power of slot 8, modulo the
context's modulus, from one in slot 3 and `R² mod M` in slot 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges an exponentiation changes. -/
abbrev pwR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(winOff, 4), (lo len (.slot c 1), 3 * bc len c + 56), (lo len (.slot c 5), bc len c),
    (lo len (.slot c 6), bc len c), (lo len (.slot c 7), bc len c), (lo len (.slot c 8), bc len c),
    (te len c 0, 16 * bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- Slot `j` lies apart from the other slots from 3 to 8 and past slot 1's range. -/
theorem slot_apart (len : Nat) (c : Ctx) {o j : Nat} (hne : j ≠ o) :
    lo len (.slot c j) + bc len c ≤ lo len (.slot c o) ∨ lo len (.slot c o) + bc len c ≤ lo len (.slot c j) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  have ej : lo len (.slot c j) = numBase + j * st len c := rfl
  have eo : lo len (.slot c o) = numBase + o * st len c := rfl
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := Nat.mul_le_mul_right (st len c) (show j + 1 ≤ o by omega_arith)
    rw [Nat.succ_mul] at this; omega_arith
  · have := Nat.mul_le_mul_right (st len c) (show o + 1 ≤ j by omega_arith)
    rw [Nat.succ_mul] at this; omega_arith

theorem slot_past1 (len : Nat) (c : Ctx) {j : Nat} (hj3 : 3 ≤ j) :
    lo len (.slot c 1) + (3 * bc len c + 56) ≤ lo len (.slot c j) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  have ej : lo len (.slot c j) = numBase + j * st len c := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have := Nat.mul_le_mul_right (st len c) hj3
  omega_arith

/-- A product into slot `o` keeps the other slots from 3 to 8. -/
theorem mulR_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem} {o j : Nat}
    (F : Frame (frameR base sp (mulR len c o)) m m') (R : CallRoom sp base bytes) (ho3 : 3 ≤ o) (ho : o ≤ 8)
    (hj3 : 3 ≤ j) (hj : j ≤ 8) (hne : j ≠ o) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega_arith
  obtain o8 : lo len (.slot c o) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) ho; simp only [lo]; omega_arith
  obtain a := slot_apart len c hne
  obtain p1 := slot_past1 len c hj3
  obtain p1o := slot_past1 len c ho3
  refine frameR_val32 F R nw (by omega_arith) ?_ ?_ <;>
    intro p hp <;> simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith

/-- The table keeps slots 3 to 8 but 7. -/
theorem tabR_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem} {j : Nat}
    (F : Frame (frameR base sp (tabR len c)) m m') (R : CallRoom sp base bytes)
    (hj3 : 3 ≤ j) (hj : j ≤ 8) (h7 : j ≠ 7) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  obtain T := h.table_fit c
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega_arith
  obtain a := slot_apart len c (o := 7) h7
  obtain p1 := slot_past1 len c hj3
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  refine frameR_val32 F R nw (by omega_arith) ?_ (tabR_fit h c)
  intro p hp; simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem pwR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ pwR len c, p.1 + p.2 ≤ bytes := by
  obtain fw := wR_fit h c
  obtain ft := tabR_fit h c
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e5 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fw _ (by simp)
  · exact fw _ (by simp)
  · dsimp only; omega_arith
  · exact fw _ (by simp)
  · exact fw _ (by simp)
  · exact fw _ (by simp)
  · exact ft _ (by simp)

/-- An exponentiation over the `N` windows `count` sets: slot 6 set to slot 5 to the power of the top
`4 N` bits of slot 8, modulo `M`. -/
theorem windowPowerWith_ok (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    (h4 : sv s.mem base len c 4 = 2 ^ (16 * bc len c) % M) {count : List Instr} {N : Nat} (hN0 : 0 < N)
    (hN : N ≤ 2 * bc len c)
    (hc : ∀ t, CtxOk Ex base bytes len args c M t → WP isa (.block count) t fun u =>
      Keeps [.esi] t u ∧ u.mem = t.mem ∧ u.gpr .esi = BitVec.ofNat 32 N) :
    WP isa (windowPowerWith c count) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (pwR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len c 6 = sv s.mem base len c 5 ^ (sv s.mem base len c 8 * 16 ^ N / 2 ^ (32 * cwc len c)) % M := by
  have h := C.inp
  have hM := C.gt
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  obtain hb := bc_le h.upper' c
  obtain RR : 2 ^ (16 * bc len c) = 2 ^ (8 * bc len c) * 2 ^ (8 * bc len c) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  unfold windowPowerWith
  -- One in Montgomery form into slot 6.
  refine WP.seq (WP.mono (cmul_ok C (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact hM)) fun s₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  obtain Y₁ : sv s₁.mem base len c 6 = 2 ^ (8 * bc len c) % M := by
    obtain v := VG.Proof.Bignum.mont_cancel C.coprime (o := sv s₁.mem base len c 6) (c := 2 ^ (8 * bc len c))
      (by rw [V₁, h4, h3, Nat.mul_one, Nat.mod_mod, RR])
    rwa [Nat.mod_eq_of_lt L₁] at v
  obtain m3₁ := mulR_sv h F₁ h.room (o := 6) (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m4₁ := mulR_sv h F₁ h.room (o := 6) (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m5₁ := mulR_sv h F₁ h.room (o := 6) (j := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m8₁ := mulR_sv h F₁ h.room (o := 6) (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The base in Montgomery form.
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [m4₁, h4]; exact Nat.mod_lt _ (by omega_arith))) fun s₂ ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  obtain B₂ : sv s₂.mem base len c 5 = sv s.mem base len c 5 * 2 ^ (8 * bc len c) % M := by
    obtain v := VG.Proof.Dsa.mont_scale C.coprime (out := sv s₂.mem base len c 5) (input := sv s.mem base len c 5)
      (c := 2 ^ (8 * bc len c)) (by rw [V₂, m5₁, m4₁, h4, RR])
    rwa [Nat.mod_eq_of_lt L₂] at v
  have h₁ := C₁.inp
  obtain m3₂ := mulR_sv h₁ F₂ h₁.room (o := 5) (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m6₂ := mulR_sv h₁ F₂ h₁.room (o := 5) (j := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m8₂ := mulR_sv h₁ F₂ h₁.room (o := 5) (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (buildTable_ok C₂ (b := sv s.mem base len c 5) (by rw [m6₂, Y₁]) B₂) fun s₃ I₃ => ?_)
  have h₂ := C₂.inp
  obtain m3₃ := tabR_sv h₂ I₃.frame h₂.room (j := 3) (by decide) (by decide) (by decide)
  obtain m6₃ := tabR_sv h₂ I₃.frame h₂.room (j := 6) (by decide) (by decide) (by decide)
  obtain m8₃ := tabR_sv h₂ I₃.frame h₂.room (j := 8) (by decide) (by decide) (by decide)
  -- The count of windows.
  have C₃ := I₃.ctx
  refine WP.seq (WP.mono (hc s₃ C₃) fun s₅ ⟨K₅, mem₅, esi₅⟩ => ?_)
  obtain C₅ : CtxOk Ex base bytes len args c M s₅ := C₃.regs K₅ mem₅
  let P := 2 ^ (32 * cwc len c)
  let E := sv s.mem base len c 8
  let b := sv s.mem base len c 5
  obtain E₅ : sv s₅.mem base len c 8 = E := by rw [sv, mem₅]; simp only [sv] at m8₃ m8₂ m8₁ ⊢; rw [m8₃, m8₂, m8₁]
  obtain Y₅ : sv s₅.mem base len c 6 = 2 ^ (8 * bc len c) % M := by
    rw [sv, mem₅]; simp only [sv] at m6₃ m6₂ Y₁ ⊢; rw [m6₃, m6₂, Y₁]
  obtain T₅ : ∀ j < 16, val32 s₅.mem base (te len c j) (cwc len c) = b ^ j * 2 ^ (8 * bc len c) % M := by
    intro j hj; rw [mem₅]; exact I₃.table j hj
  obtain one₅ : sv s₅.mem base len c 3 = 1 := by
    rw [sv, mem₅]; simp only [sv] at m3₃ m3₂ m3₁ h3 ⊢; rw [m3₃, m3₂, m3₁, h3]
  obtain hE : E < P := val32_lt _ _ _ _
  -- The windows.
  refine WP.seq (WP.mono (PublicRt.countLoop (N := N) (by omega_arith) (fun j t =>
      CtxOk Ex base bytes len args c M t ∧ Frame (frameR base (s₅.gpr .esp) (wR len c)) s₅.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₅ t ∧ t.gpr .esi = BitVec.ofNat 32 (N - j) ∧
      (∀ j' < 16, val32 t.mem base (te len c j') (cwc len c) = b ^ j' * 2 ^ (8 * bc len c) % M) ∧
      sv t.mem base len c 8 = E * 16 ^ j % P ∧
      sv t.mem base len c 6 = b ^ (E * 16 ^ j / P) * 2 ^ (8 * bc len c) % M)
    (fun j t hj ⟨Ct, Ft, Kt, et, Tt, Et, Yt⟩ => WP.mono (windowStep_ok Ct Tt Yt (by omega_arith) (by omega_arith) et)
      fun u ⟨Cu, Fu, Ku, eu, zu, Yu, Eu⟩ => ?_)
    ⟨C₅, Frame.refl _ _, Keeps.refl _ _, by rw [esi₅, Nat.sub_zero], T₅,
      by rw [E₅, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hE],
      by rw [Y₅, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hE, Nat.pow_zero, Nat.one_mul]⟩)
    fun s₆ I₆ => ?_)
  · have sp : t.gpr .esp = s₅.gpr .esp := Kt.1 _ (by decide)
    rw [sp] at Fu
    obtain ⟨_, Tu⟩ := wR_keep Ct.inp Fu (sp ▸ Ct.inp.room)
    refine ⟨⟨Cu, Ft.trans Fu, Kt.trans Ku, by rw [eu, Nat.sub_sub], fun j' hj' => by rw [Tu j' hj', Tt j' hj'], ?_, ?_⟩,
      by rw [zu]; congr 1; exact decide_eq_decide.mpr (by omega_arith)⟩
    · rw [Eu, Et, Nat.pow_succ, ← Nat.mul_assoc, Nat.mod_mul_mod]
    · rw [Yu, Et, VG.Proof.Mont.X86.Dynamic.window_power, Nat.pow_succ, ← Nat.mul_assoc,
        VG.Proof.Mont.X86.Dynamic.window_exponent (E * 16 ^ j) _ (Nat.two_pow_pos _)]
  obtain ⟨C₆, F₆, K₆, _, _, E₆, Y₆⟩ := I₆
  -- Out of Montgomery form.
  obtain sp₆ : s₆.gpr .esp = s₅.gpr .esp := K₆.1 _ (by decide)
  obtain ⟨one₆, _⟩ := wR_keep C₅.inp F₆ C₅.inp.room
  refine WP.mono (cmul_ok C₆ (o := 6) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [one₆, one₅]; exact hM)) fun u ⟨Cu, Ku, Fu, Lu, Vu⟩ => ⟨Cu, ?_, ?_, ?_⟩
  · have sp₁ : s₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    obtain sp₂ : s₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    obtain sp₃ : s₃.gpr .esp = s.gpr .esp := (I₃.keeps.1 _ (by decide)).trans sp₂
    obtain sp₅ : s₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), sp₃]
    rw [sp₁] at F₂
    have F₃ := I₃.frame
    rw [sp₂] at F₃
    rw [sp₆, sp₅] at Fu
    rw [sp₅] at F₆
    obtain sub : ∀ {ws : List (Nat × Nat)}, (∀ p ∈ ws, p ∈ pwR len c) → ∀ {m m' : Mem},
        Frame (frameR base (s.gpr .esp) ws) m m' → Frame (frameR base (s.gpr .esp) (pwR len c)) m m' :=
      fun hs _ _ F => frameR_mono F hs
    obtain m6 : ∀ p ∈ mulR len c 6, p ∈ pwR len c := by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    obtain m5 : ∀ p ∈ mulR len c 5, p ∈ pwR len c := by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    obtain mt : ∀ p ∈ tabR len c, p ∈ pwR len c := by
      intro p hp; simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp
    obtain mw : ∀ p ∈ wR len c, p ∈ pwR len c := by
      intro p hp; simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp
    exact ((((sub m6 F₁).trans (sub m5 F₂)).trans (sub mt F₃)).trans
      (by rw [← mem₅]; exact sub mw F₆)).trans (sub m6 Fu)
  · exact (((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans I₃.keeps).trans
      (K₅.mono (by decide))).trans K₆).trans (Ku.mono (by decide))
  · have fin := Y₆
    obtain v := VG.Proof.Dsa.mont_decode (A := sv s₆.mem base len c 6) (out := sv u.mem base len c 6) C.coprime
      (by rw [fin, Nat.mod_mod]) (by rw [Vu, one₆, one₅])
    rw [Nat.mod_eq_of_lt Lu] at v
    exact v

/-- An exponentiation: slot 6 set to slot 5 to the power of slot 8, modulo `M`. -/
theorem windowPower_ok (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    (h4 : sv s.mem base len c 4 = 2 ^ (16 * bc len c) % M) :
    WP isa (windowPower c) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (pwR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len c 6 = sv s.mem base len c 5 ^ sv s.mem base len c 8 % M := by
  have h := C.inp
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  obtain hb := bc_le h.upper' c
  refine WP.mono (windowPowerWith_ok C h3 h4 (N := 2 * bc len c) (by omega_arith) (Nat.le_refl _) fun t Ct =>
    widthC_ok (k := 0) (c := c) (r := .esi) (is := [_]) Ct.inp.width h.upper' fun s₄ K₄ M₄ e₄ =>
      wp_addS rfl fun s₅ a₅ _ => WP.block_nil ⟨K₄.trans (a₅.keeps.mono (by decide)), by rw [a₅.mem, M₄], by
        rw [a₅.gpr, e₄, BitVec.ofNat_add_ofNat]; congr 1; omega_arith⟩) fun u ⟨Cu, Fu, Ku, Vu⟩ => ⟨Cu, Fu, Ku, ?_⟩
  rw [Vu, show 2 * bc len c = 8 * cwc len c by omega_arith, VG.Proof.Mont.X86.Dynamic.window_all]

end

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! # What the stages of private CRT share

Frames widened to ranges that contain theirs (`frameR_widen`), the low words
of a number below their range (`val32_low`), a context made from a factor
(`factorCtx_ok`: the factor copied into slot 0 and the context prepared), and
the result of a power saved zero-extended (`saveResult_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem frameR_widen {base : Addr} {sp : BitVec 32} {ws ws' : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hw : ∀ p ∈ ws, ∃ q ∈ ws', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) :
    Frame (frameR base sp ws') m m' :=
  F.sub fun r hr => by
    simp only [frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · obtain ⟨q, hq, h1, h2⟩ := hw p hp
      exact ⟨⟨off base q.1, q.2⟩, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩),
        VG.Offset.sub base h1 h2⟩

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- `2 B` and `B` bytes from wide slot 9 on; half slots within the wide ones. -/
theorem In.wide_fit (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 19) :
    lo len (.slot .wide j) + 2 * bc len .wide + 32 ≤ lo len (.slot .wide (j + 1)) ∧
      lo len (.slot .wide (j + 1)) ≤ bytes := by
  have f := h.slot_fit .wide (j := j) (by omega_using [hj])
  have e : lo len (.slot .wide (j + 1)) = lo len (.slot .wide j) + st len .wide := by
    simp only [lo]; rw [Nat.succ_mul]; omega_using []
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  omega_using [f, e, est]

/-- The half context's slots, its table and the wide context's slots 0 to 8, within the first nine
wide slots and the table. -/
theorem half_in_wide (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 8) :
    lo len (.slot .half j) + st len .half ≤ lo len (.slot .wide 9) := by
  have hb := bc_half_le' len
  have g := bc_ge h.lower' .wide
  have e : lo len (.slot .half j) = numBase + j * st len .half := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have sh : st len .half = 2 * bc len .half + 32 := rfl
  have sw : st len .wide = 2 * bc len .wide + 32 := rfl
  have := Nat.mul_le_mul_right (st len .half) hj
  rw [e, e9]; omega_using [hb, g, sh, sw, this]

theorem prepR_fit2 (h : In Ex base bytes len args s) (c : Ctx) :
    (∀ p ∈ prepR len c, p.1 + p.2 ≤ bytes) ∧ ∀ p ∈ baseR len c, p.1 + p.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le c (by decide)
  have e13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 2) := sl_le c (by decide)
  have e23 : lo len (.slot c 2) + st len c ≤ lo len (.slot c 3) := sl_le c (by decide)
  have e3 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e4 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e7 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have nb : numBase = 3336 := rfl
  constructor <;> intro p hp <;> simp only [prepR, baseR, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [invOff] <;> omega_arith

theorem prepR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ prepR len c, p.1 + p.2 ≤ bytes :=
  (prepR_fit2 h c).1

theorem baseR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ baseR len c, p.1 + p.2 ≤ bytes :=
  (prepR_fit2 h c).2

/-- The squares of `prepare`, by the shared squaring loop: from `2^(8 Bc + d) mod M` in slot 4,
`2^(8 Bc + 64 d) mod M`. -/
theorem squares4_ok {c : Ctx} {M d : Nat} {s : State} (C : CtxOk Ex base bytes len args c M s)
    (h4 : sv s.mem base len c 4 = 2 ^ (8 * bc len c + d) % M) :
    WP isa (VG.Impl.Mont.X86.Dynamic.repeatSquaresWith (mul c 4 4 4) 6) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Keeps [.eax, .ecx, .edx, .esi] s u ∧
      Frame (frameR base (s.gpr .esp) (mulR len c 4)) s.mem u.mem ∧
      sv u.mem base len c 4 = 2 ^ (8 * bc len c + 64 * d) % M := by
  have hM := C.gt
  let P : State → Prop := fun u => CtxOk Ex base bytes len args c M u ∧ Keeps [.eax, .ecx, .edx, .esi] s u ∧
    Frame (frameR base (s.gpr .esp) (mulR len c 4)) s.mem u.mem
  let num : State → Nat := fun u => sv u.mem base len c 4
  have stable (u v : State) (U : P u) (mem : v.mem = u.mem) (keep : Keeps [.esi] u v) : P v :=
    ⟨U.1.regs keep mem, U.2.1.trans (keep.mono (by decide)), by rw [mem]; exact U.2.2⟩
  have step (u : State) (U : P u) (lt : num u < M) :
      WP isa (mul c 4 4 4) u fun v =>
        P v ∧ Keeps VG.Proof.Mont.X86.clob u v ∧ num v < M ∧ num v * 2 ^ (8 * bc len c) % M = num u * num u % M := by
    refine WP.mono (cmul_ok U.1 (o := 4) (a := 4) (b := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) lt) fun v ⟨Cv, Kv, Fv, Lv, Vv⟩ => ?_
    have spu : u.gpr .esp = s.gpr .esp := U.2.1.1 _ (by decide)
    exact ⟨⟨Cv, U.2.1.trans (Kv.mono (by decide)), U.2.2.trans (by rw [← spu]; exact Fv)⟩, Kv.mono (by decide), Lv, Vv⟩
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.repeatSquaresWith_ok (mul c 4 4 4) P num (E := d) C.coprime stable
    (fun u v h => by simp only [num, sv]; rw [h]) step (by decide) (by decide)
    ⟨C, Keeps.refl _ _, Frame.refl _ _⟩ (by simp only [num]; rw [h4]; exact Nat.mod_lt _ (by omega_using [hM]))
    (by simp only [num]; rw [h4, Nat.pow_add, Nat.mul_comm, Nat.mod_mod]))
    fun t ⟨⟨Ct, Kt, Ft⟩, lt, value⟩ => ⟨Ct, Kt, Ft, ?_⟩
  simp only [num] at lt value
  rw [Nat.mod_eq_of_lt lt] at value
  rw [value, Nat.pow_add, Nat.mul_comm]

/-- A prepared context: its modulus the odd number above one that slot 0 held (or three), one in
slot 3 and `R² mod M` in slot 4. -/
theorem prepCtx_ok (h : In Ex base bytes len args s) (c : Ctx) :
    WP isa (prepare c) s fun u =>
      CtxOk Ex base bytes len args c (safeM (sv s.mem base len c 0)) u ∧ sv u.mem base len c 3 = 1 ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) ∧
      Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw := h.scratch.nowrap
  have fit := prepR_fit2 h c
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e12 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 2) := sl_le c (by decide)
  have e23 : lo len (.slot c 2) + st len c ≤ lo len (.slot c 3) := sl_le c (by decide)
  have e34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  have d8 := bc_dvd len c
  have e48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  refine WP.seq (WP.mono (prepBase_ok h c) fun u ⟨F, M, one, R2, I, K⟩ => ?_)
  have C : CtxOk Ex base bytes len args c (safeM (sv s.mem base len c 0)) u :=
    ⟨h.keepF K (by decide) (by decide) F fit.2, M, safeM_gt _, safeM_odd _, I⟩
  have spu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.mono (squares4_ok C (d := bc len c / 8) R2) fun t ⟨Ct, Kt, Ft, Vt⟩ => ⟨Ct, ?_, ?_, ?_, ?_⟩
  · have v := frameR_val32 (d := lo len (.slot c 3)) (k := cwc len c) Ft C.inp.room nw (by omega_using [f8, bw, est, e34, e48]) (by
      intro p hp
      simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) (fun p hp => fit.1 p (by
        simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp))
    simp only [sv] at one ⊢
    rw [v, one]
  · rw [Vt]; congr 2; omega_using [d8]
  · have W : Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem u.mem := frameR_widen F fun p hp => by
      simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨(invOff, 4), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot c 0), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot c 1), 3 * bc len c + 56), by simp, Nat.le_refl _, by dsimp only; omega_using []⟩
      · exact ⟨(lo len (.slot c 3), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot c 4), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot c 7), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
    refine W.trans ?_
    rw [← spu]
    exact frameR_mono Ft fun p hp => by
      simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp
  · exact K.trans (Kt.mono (by decide))

/-- A power's result (slot 6 of `c`) into the wide slot `o`, zero-extended to `2 B` bytes. -/
theorem saveResultAt_ok (h : In Ex base bytes len args s) (c : Ctx) {o : Nat} (ho : o ≤ 19)
    (e69 : lo len (.slot c 6) + bc len c ≤ lo len (.slot .wide o)) :
    WP isa (saveResult c o) s fun u =>
      Outside base (lo len (.slot .wide o)) (2 * bc len .wide) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = sv s.mem base len c 6 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have W := h.wide_fit (j := o) ho
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have bc' := bc_eq_cwc len c
  have hb := bc_half_le' len
  have g := bc_ge h.lower' .wide
  have hcw : bc len c ≤ bc len .wide := by cases c <;> omega_arith
  have bl := h.bytes_lt
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega_using [bw]
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  unfold saveResult
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide o) (two_ok .wide) (by rw [cb2]; omega_using [W]))
    fun u₁ ⟨O₁, Z₁, K₁⟩ => ?_)
  rw [cb2, cw2] at *
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_using [W]))
  refine WP.mono (copy_ok h₁ (x := .slot c 6) (d := .slot .wide o) (one_ok c) (by rw [cb1]; omega_using [e69, W])
    (by rw [cb1]; omega_using [W, hcw]) (by rw [cb1]; exact .inr e69)) fun u ⟨O₂, V₂, K₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [cb1] at O₂; exact O₁.trans (O₂.mono (Nat.le_refl _) (by omega_using [hcw]))
  · rw [cb1] at O₂
    rw [cw1] at V₂
    have hz : val32 u₁.mem base (lo len (.slot .wide o) + 4 * cwc len c) (2 * cwc len .wide - cwc len c) = 0 := by
      have z := Z₁
      rw [show 2 * cwc len .wide = cwc len c + (2 * cwc len .wide - cwc len c) by omega, val32_append] at z
      rcases Nat.eq_zero_of_add_eq_zero z with ⟨_, z2⟩
      exact (Nat.mul_eq_zero.mp z2).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
    rw [show 2 * cwc len .wide = cwc len c + (2 * cwc len .wide - cwc len c) by omega,
      val32_ext (by rw [O₂.val32 (.inr (by omega_using [bc'])) (by omega_using [e69, W, bw, bc', bl])]; exact hz), V₂]
    simp only [sv]
    exact O₁.val32 (.inl (by omega_using [e69, bc'])) (by omega_using [e69, W, bc', bl])
  · exact (K₁.mono (by decide)).trans K₂

theorem saveResult_ok (h : In Ex base bytes len args s) (c : Ctx) {o : Nat} (ho9 : 9 ≤ o) (ho : o ≤ 19) :
    WP isa (saveResult c o) s fun u =>
      Outside base (lo len (.slot .wide o)) (2 * bc len .wide) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = sv s.mem base len c 6 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  refine saveResultAt_ok h c ho ?_
  have e6 : lo len (.slot c 6) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e89 : lo len (.slot c 8) + st len c ≤ lo len (.slot .wide 9) := by
    cases c with
    | half => exact half_in_wide h (j := 8) (by decide)
    | wide => exact sl_le (i := 8) (j := 9) .wide (by decide)
  have : lo len (.slot .wide 9) ≤ lo len (.slot .wide o) := by
    have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
    have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
    have := Nat.mul_le_mul_right (st len .wide) ho9; omega_using [e9, eo, this]
  have est : st len c = 2 * bc len c + 32 := rfl
  omega_using [e6, e89, this, est]

end

end VG.Proof.Bignum.X86.CrtRt
