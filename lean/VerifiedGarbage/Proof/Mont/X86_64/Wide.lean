import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Mont.X86_64.Chain

/-!
# Montgomery arithmetic on x86-64: the accumulator in memory

For more than six words, the accumulator of `mulW` keeps its `n` low words in
the temporary area and its two top words in `r9` and `r10`. The pieces: a
multiply-accumulate step into a word of memory (`memStep_ok`), a row of them
(`memRow_ok`), the words moved down by one (`moveDown_ok`, `shiftDown_ok`),
and the cleared area (`zeroWords_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono mulStep_ok)

/-- `sub_regs`, also when `simp` alone closes the goal. -/
macro "sub_regs'" : tactic => `(tactic| (intro q hq; simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, List.not_mem_nil, or_false] at hq ⊢; first | done | grind))

/-! ## Loads and stores -/

/-- `r = [d]`. -/
theorem movMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun s' =>
      s'.gpr r = word s.mem base d ∧ s'.cf = s.cf ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.cf_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, hq, ite_false]

/-- `[d] = r`. -/
theorem storeReg_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.store (sc d) r]) s fun s' =>
      s'.mem = s.mem.writeW (off base d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.cf = s.cf ∧
        KeepRegs [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_sc hs hd, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, ⟨fun _ _ => rfl, rfl, rfl⟩⟩

/-- The `k` words at `d` of memory changed only at `t`, apart from them. -/
theorem wordsVal_apart {base : Addr} {m m' : Mem} {t n d k : Nat} (h : Outside base t n m m')
    (hd : d + 8 * k ≤ t ∨ t + n ≤ d) (hn : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' base d k = wordsVal m base d k := h.wordsVal hd hn

/-! ## Multiply-accumulate into memory -/

/-- `[t] + 2⁶⁴ rbp' = [t] + rbp + rcx · [d]`, through `r8`. -/
theorem memStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t d : Nat}
    (ht : t + 8 ≤ size) (hd : d + 8 ≤ size) :
    WP isa (.block (memStep t (.mem (sc d)))) s fun s' =>
      (word s'.mem base t).toNat + 2 ^ 64 * (s'.gpr .rbp).toNat =
        (word s.mem base t).toNat + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * (word s.mem base d).toNat ∧
      s'.mem = s.mem.writeW (off base t) (word s'.mem base t) ∧
      KeepRegs [.r8, .rbp, .rax, .rdx] s s' := by
  rw [memStep, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 ht) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  have hsrc : readSrc s₁ (.mem (sc d)) = some (word s.mem base d) := by
    rw [readSrc_sc hs₁ hd, k₁.2.1]
  refine WP.mono (mulStep_ok s₁ hsrc (t := .r8) (c := .rbp) (ai := .rcx) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (storeReg_ok hs₂ .r8 ht) fun s₃ ⟨m₃, g₃, _, k₃⟩ => ?_
  have hw : word s₃.mem base t = s₂.gpr .r8 := by rw [m₃, word_writeW_self]
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  refine ⟨?_, by rw [hw, m₃, hm₂], ?_⟩
  · rw [hw, g₃, e₂, l₁, k₁.1 .rbp (by decide), k₁.1 .rcx (by decide)]
  · exact (((Keeps.regs k₁).mono (by sub_regs')).trans ((Keeps.regs k₂).mono (by sub_regs'))).trans
      (k₃.mono (by sub_regs'))

/-- `k` words at `t` `+= rcx · [d]` with the carry word `rbp` in and out. -/
theorem memSteps_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {t d : Nat},
    Scr s base size → t + 8 * k ≤ size → d + 8 * k ≤ size → (d + 8 * k ≤ t ∨ t + 8 * k ≤ d) →
    WP isa (.block (memSteps k t d)) s fun s' =>
      wordsVal s'.mem base t k + 2 ^ (64 * k) * (s'.gpr .rbp).toNat =
        wordsVal s.mem base t k + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * wordsVal s.mem base d k ∧
      KeepRegs [.r8, .rbp, .rax, .rdx] s s' ∧ Outside base t (8 * k) s.mem s'.mem
  | 0, s, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [wordsVal], ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, s, base, t, d, hs, ht, hd, hsep => by
    have hn := hs.nowrap
    rw [memSteps, WP.block_append_iff]
    refine WP.mono (memStep_ok hs (t := t) (d := d) (by omega) (by omega)) fun s₁ ⟨e₁, m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base t 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (memSteps_ok k hs₁ (t := t + 8) (d := d + 8) (by omega) (by omega) (by omega))
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    have hT₁ : wordsVal s₁.mem base (t + 8) k = wordsVal s.mem base (t + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    have hD₁ : wordsVal s₁.mem base (d + 8) k = wordsVal s.mem base (d + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    have hD₀ : word s₁.mem base d = word s.mem base d := O₁.word (by omega) (by omega)
    have hw₂ : word s₂.mem base t = word s₁.mem base t := O₂.word (by omega) (by omega)
    have hc₁ : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr .rcx (by decide)
    rw [hT₁, hD₁, hc₁] at e₂
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    simp only [wordsVal, pow64_succ, hw₂]
    have h1 : (s.gpr .rcx).toNat * ((word s.mem base d).toNat + 2 ^ 64 * wordsVal s.mem base (d + 8) k) =
        (s.gpr .rcx).toNat * (word s.mem base d).toNat +
          2 ^ 64 * ((s.gpr .rcx).toNat * wordsVal s.mem base (d + 8) k) := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    have h2 : 2 ^ 64 * 2 ^ (64 * k) * (s₂.gpr .rbp).toNat =
        2 ^ 64 * (2 ^ (64 * k) * (s₂.gpr .rbp).toNat) := Nat.mul_assoc _ _ _
    rw [h1, h2]
    omega

/-- A row: the carry word cleared, then `memSteps`. -/
theorem memRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k t d : Nat}
    (ht : t + 8 * k ≤ size) (hd : d + 8 * k ≤ size) (hsep : d + 8 * k ≤ t ∨ t + 8 * k ≤ d) :
    WP isa (.block (memRow k t d)) s fun s' =>
      wordsVal s'.mem base t k + 2 ^ (64 * k) * (s'.gpr .rbp).toNat =
        wordsVal s.mem base t k + (s.gpr .rcx).toNat * wordsVal s.mem base d k ∧
      KeepRegs [.r8, .rbp, .rax, .rdx] s s' ∧ Outside base t (8 * k) s.mem s'.mem := by
  rw [memRow, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zeros_ok s [.rbp]) fun s₁ ⟨z₁, k₁⟩ => ?_
  refine WP.mono (memSteps_ok k (hs.of_keeps k₁ (by decide)) ht hd hsep) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [z₁ .rbp (by simp), k₁.2.1, k₁.1 .rcx (by decide)] at e₂
  exact ⟨by simpa using e₂, ((Keeps.regs k₁).mono (by sub_regs')).trans k₂, k₁.2.1 ▸ O₂⟩

/-! ## Moving the words down -/

/-- `[t + 8 j] = [t + 8 (j + 1)]` for `j < k`. -/
theorem moveDown_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {t : Nat},
    Scr s base size → t + 8 * (k + 1) ≤ size →
    WP isa (.block (moveDown k t)) s fun s' =>
      wordsVal s'.mem base t k = wordsVal s.mem base (t + 8) k ∧
      KeepRegs [.r8] s s' ∧ Outside base t (8 * k) s.mem s'.mem
  | 0, s, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, s, base, t, hs, ht => by
    have hn := hs.nowrap
    rw [moveDown, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movMem_ok hs .r8 (d := t + 8) (by omega)) fun s₁ ⟨l₁, _, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    refine WP.mono (storeReg_ok hs₁ .r8 (d := t) (by omega)) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
    have hs₂ := hs₁.of_keepRegs k₂ (by decide)
    have O₂ : Outside base t 8 s.mem s₂.mem := by
      rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (moveDown_ok k hs₂ (t := t + 8) (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
    have hw₃ : word s₃.mem base t = word s.mem base (t + 8) := by
      rw [O₃.word (by omega) (by omega), m₂, word_writeW_self, l₁]
    have hS : wordsVal s₂.mem base (t + 8 + 8) k = wordsVal s.mem base (t + 8 + 8) k :=
      O₂.wordsVal (by omega) (by omega)
    refine ⟨?_, (((Keeps.regs k₁).mono (by sub_regs')).trans (k₂.mono (by sub_regs'))).trans k₃,
      fun x hx => by rw [O₃ x (by omega), O₂ x (by omega)]⟩
    rw [wordsVal, wordsVal, hw₃, e₃, hS]

/-- The accumulator `[tmp] + 2^(64 n) (r9 + 2⁶⁴ r10)` divided by `2⁶⁴` (its
low word, which is dropped, is zero): the words moved down, `r9` on top,
`r10` into `r9`, and `r10` cleared. -/
theorem shiftDown_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : 0 < M.n) (htmp : M.tmp + 8 * M.n ≤ size) :
    WP isa (.block (shiftDown M)) s fun s' =>
      wordsVal s'.mem base M.tmp M.n =
        wordsVal s.mem base (M.tmp + 8) (M.n - 1) + 2 ^ (64 * (M.n - 1)) * (s.gpr .r9).toNat ∧
      s'.gpr .r9 = s.gpr .r10 ∧ s'.gpr .r10 = 0 ∧
      KeepRegs [.r8, .r9, .r10] s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [shiftDown, WP.block_append_iff]
  refine WP.mono (moveDown_ok (M.n - 1) hs (t := M.tmp) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeReg_ok hs₁ .r9 (d := M.tmp + 8 * (M.n - 1)) (by omega))
    fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have O₂ : Outside base (M.tmp + 8 * (M.n - 1)) 8 s₁.mem s₂.mem := by
    rw [m₂]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (show WP isa (.block [.mov .r9 (.reg .r10), .mov32 .r10 (.imm 0)]) s₂
      (fun s₃ => s₃.gpr .r9 = s₂.gpr .r10 ∧ s₃.gpr .r10 = 0 ∧ Keeps [.r9, .r10] s₂ s₃) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, reduceCtorEq, ite_false, Option.some.injEq,
      exists_eq_left']
    refine ⟨by trivial, by trivial, fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, hq.1, hq.2, ite_false]) fun s₃ ⟨r9₃, r10₃, k₃⟩ => ?_
  have hr9 : s₁.gpr .r9 = s.gpr .r9 := k₁.gpr .r9 (by decide)
  have hr10 : s₂.gpr .r10 = s.gpr .r10 := by rw [g₂, k₁.gpr .r10 (by decide)]
  refine ⟨?_, by rw [r9₃, hr10], r10₃, (k₁.mono (by sub_regs')).trans
    ((k₂.mono (by sub_regs')).trans ((Keeps.regs k₃).mono (by sub_regs'))), fun x hx => ?_⟩
  · have hsplit := wordsVal_succ_top s₃.mem base M.tmp (M.n - 1)
    rw [show M.n - 1 + 1 = M.n by omega] at hsplit
    rw [hsplit, k₃.2.1, m₂, word_writeW_self,
      (writeW_outside s₁.mem base (d := M.tmp + 8 * (M.n - 1)) (s₁.gpr .r9) (by omega)).wordsVal
        (by omega) (by omega), e₁, hr9]
  · rw [k₃.2.1, O₂ x (by omega), O₁ x (by omega)]

/-! ## Clearing -/

/-- `k` words of zeros at `t`. -/
theorem zeroWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k t : Nat}
    (ht : t + 8 * k ≤ size) :
    WP isa (.block (zeroWords k t)) s fun s' =>
      wordsVal s'.mem base t k = 0 ∧ KeepRegs [.r8] s s' ∧ Outside base t (8 * k) s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [zeroWords, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zeros_ok s [.r8]) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8 : s₁.gpr .r8 = 0 := z₁ .r8 (by simp)
  -- Each store keeps `r8` zero; induct over the words from the top.
  have key : ∀ j ≤ k, ∀ {u : State}, Scr u base size → u.gpr .r8 = 0 →
      WP isa (.block (((List.range k).drop (k - j)).map fun i => Instr.store (sc (t + 8 * i)) .r8)) u
        fun u' => wordsVal u'.mem base (t + 8 * (k - j)) j = 0 ∧ u'.gpr = u.gpr ∧
          KeepRegs [] u u' ∧ Outside base (t + 8 * (k - j)) (8 * j) u.mem u'.mem := by
    intro j
    induction j with
    | zero => intro _ u _ _; rw [Nat.sub_zero, List.drop_of_length_le (by simp)]
              exact WP.block_nil ⟨rfl, rfl, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
    | succ j ih =>
      intro hj u hu h0
      rw [List.drop_eq_getElem_cons (by simp; omega), List.map_cons, ← List.singleton_append,
        WP.block_append_iff]
      simp only [List.getElem_range]
      refine WP.mono (storeReg_ok hu .r8 (d := t + 8 * (k - (j + 1))) (by omega))
        fun u₁ ⟨m₁, g₁, _, k₁'⟩ => ?_
      have hu₁ := hu.of_keepRegs k₁' (by decide)
      rw [show k - (j + 1) + 1 = k - j by omega]
      refine WP.mono (ih (by omega) hu₁ (by rw [g₁, h0])) fun u₂ ⟨e₂, g₂, k₂, O₂⟩ => ?_
      have O₁ : Outside base (t + 8 * (k - (j + 1))) 8 u.mem u₁.mem := by
        rw [m₁]; exact writeW_outside _ _ _ (by omega)
      refine ⟨?_, by rw [g₂, g₁], k₁'.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
      rw [wordsVal, O₂.word (by omega) (by omega), m₁, word_writeW_self, h0,
        show t + 8 * (k - (j + 1)) + 8 = t + 8 * (k - j) by omega, e₂]
      rfl
  have hk := key k (Nat.le_refl _) hs₁ h8
  rw [Nat.sub_self, List.drop_zero, Nat.mul_zero, Nat.add_zero] at hk
  refine WP.mono hk fun s₂ ⟨e₂, _, k₂, O₂⟩ => ⟨e₂, ((Keeps.regs k₁).mono (by sub_regs')).trans
    (k₂.mono (by sub_regs')), by rw [← k₁.2.1]; exact O₂⟩

end VG.Proof.Mont.X86_64
