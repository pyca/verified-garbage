import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.RegSetOrder

/-!
# Summaries for the x86 taint analysis

The x86 analysis is not monotone along its order `le`: with more known about
memory (more region bases, base-address words or stack arguments), an
access may find another region first, or a load more regions. It is
monotone along a finer order, `LeR`: the same knowledge about memory (the
lengths, the bases, the base-address words, the stack and the arguments), and
more public registers, flags and slots. So summaries (`taint_summary`,
`taint_decide_sum`) apply to code whose taint knows the same about memory as
the summary's (e.g. the body of a loop, or a function called from the same
stack), with more public registers and slots; the hints of the checks still
use `le` (`Taint.Frame`, with `R := LeR`). The analysis is `X86.taint`
itself.

A frame of a summary (what the summarized code does not write, `keeps`) is a
set of registers (`Fr` compares only registers and flags).
-/

namespace VG.X86.Taint

open RegSet

private theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

/-! ## The order -/

/-- `τ` and `σ` know the same about memory, and `σ` has at least the public
registers, flags and slots of `τ`. -/
def leR (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && KList.all τ.slots (mem3 · σ.slots) &&
    τ.lens == σ.lens && τ.bases == σ.bases && τ.wbases == σ.wbases && Nat.beq τ.argLen σ.argLen &&
    τ.argBases == σ.argBases && τ.stk == σ.stk && Nat.beq τ.room σ.room

/-- `σ` is `τ` with the registers `r`, flags `f` and slots `sl`. -/
def upd (τ : T) (r : RegSet Reg) (f : Bool) (sl : List (Nat × Nat × Nat)) : T :=
  { τ with regs := r, flags := f, slots := sl }

/-- `leR`, as a proposition. -/
structure LeR (τ σ : T) : Prop where
  regs : τ.regs.subset σ.regs = true
  flags : τ.flags = true → σ.flags = true
  slots : ∀ x ∈ τ.slots, x ∈ σ.slots
  shape : σ = upd τ σ.regs σ.flags σ.slots

theorem leR_iff {τ σ : T} : leR τ σ = true ↔ LeR τ σ := by
  simp only [leR, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, KList.all_eq,
    List.all_eq_true, mem3_eq, List.contains_iff_mem, KList.beq_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hs⟩, hl⟩, hb⟩, hw⟩, ha⟩, hab⟩, hk⟩, hro⟩
    refine ⟨hr, fun h => hf.elim (fun e => by rw [e] at h; cases h) id, hs, ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := σ
    simp only at hl hb hw ha hab hk hro
    simp only [upd, hl, hb, hw, ha, hab, hk, hro]
  · rintro ⟨hr, hf, hs, e⟩
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, ?_⟩, hs⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> (try rw [e]) <;> (try rfl)
    cases h : τ.flags
    · exact .inl rfl
    · exact .inr (hf h)

theorem LeR.refl (τ : T) : LeR τ τ := ⟨RegSet.subset_refl _, id, fun _ h => h, rfl⟩

theorem LeR.trans {a b c : T} (h₁ : LeR a b) (h₂ : LeR b c) : LeR a c where
  regs := RegSet.subset_trans h₁.regs h₂.regs
  flags h := h₂.flags (h₁.flags h)
  slots x hx := h₂.slots x (h₁.slots x hx)
  shape := by rw [h₂.shape, h₁.shape]; rfl

theorem le_of_le_leR {m τ σ : T} (hm : le m τ = true) (h : LeR τ σ) : le m σ = true := by
  rw [h.shape]
  simp only [le, upd, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, decide_eq_true_eq] at hm ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hw⟩, ha⟩, hab⟩, hk⟩, hro⟩ := hm
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨RegSet.subset_trans hr h.regs, ?_⟩, hl⟩, hb⟩, fun x hx => h.slots x (hs x hx)⟩, hw⟩,
    ha⟩, hab⟩, hk⟩, decide_eq_true hro⟩
  rcases hf with e | e
  · exact .inl e
  · exact .inr (h.flags e)

/-! ## Monotonicity -/

section
variable {τ : T} {r : RegSet Reg} {f : Bool} {sl : List (Nat × Nat × Nat)}

theorem pub_upd (hr : τ.regs.subset r = true) {x : Reg} (h : pub τ x = true) :
    pub (upd τ r f sl) x = true := RegSet.mem_of_subset hr h

theorem srcOk_upd (hr : τ.regs.subset r = true) {src : Src} (h : srcOk τ src = true) :
    srcOk (upd τ r f sl) src = true := by
  cases src <;> first | rfl | exact pub_upd hr h

theorem srcPub_upd (hr : τ.regs.subset r = true) {src : Src} (h : srcPub τ src = true) :
    srcPub (upd τ r f sl) src = true := by
  cases src <;> first | rfl | exact pub_upd hr h | cases h

theorem slotPub_upd (hsl : ∀ x ∈ τ.slots, x ∈ sl) {m : MemOp} {w : Nat} (h : slotPub τ m w = true) :
    slotPub (upd τ r f sl) m w = true := by
  unfold slotPub at h ⊢
  rw [show addrOf (upd τ r f sl) m = addrOf τ m from rfl]
  revert h
  cases addrOf τ m with
  | none => intro h; cases h
  | some id =>
    intro h
    obtain ⟨i, d⟩ := id
    simp only at h ⊢
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨x, hsl x hx, hp⟩

theorem loadPub_upd (hsl : ∀ x ∈ τ.slots, x ∈ sl) {src : Src} (h : loadPub τ src = true) :
    loadPub (upd τ r f sl) src = true := by
  cases src with
  | mem m =>
    simp only [loadPub, Bool.or_eq_true] at h ⊢
    exact h.imp (slotPub_upd hsl) id
  | _ => cases h

theorem set_upd (hr : τ.regs.subset r = true) (d : Reg) {p q : Bool} (hpq : p = true → q = true) :
    (set τ d p).subset (set (upd τ r f sl) d q) = true := by
  unfold set
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono hr d
  · exact RegSet.subset_trans (RegSet.erase_subset τ.regs d)
      (RegSet.subset_trans hr (RegSet.subset_insert r d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono hr d

theorem mem_storeSlots_true {m : MemOp} {w : Nat} {x : Nat × Nat × Nat}
    (hx : x ∈ storeSlots τ m w true) :
    x ∈ τ.slots ∨ ∃ i d, addrOf τ m = some (i, d) ∧ d + w ≤ τ.lens.getD i 0 ∧ x = (i, d, w) := by
  unfold storeSlots at hx
  cases ha : addrOf τ m with
  | none => simp only [ha, ite_true] at hx; exact .inl hx
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only [ha] at hx
    by_cases hw : d + w ≤ τ.lens.getD i 0
    · simp only [hw, ite_true, Bool.true_or, List.filter_eq_self.mpr (fun _ _ => rfl),
        List.mem_cons] at hx
      exact hx.elim (fun e => .inr ⟨i, d, rfl, hw, e⟩) .inl
    · simp only [hw, ite_false, ite_true] at hx; exact .inl hx

theorem mem_storeSlots_false {m : MemOp} {w : Nat} {x : Nat × Nat × Nat}
    (hx : x ∈ storeSlots τ m w false) :
    x ∈ τ.slots ∧ ∃ i d, addrOf τ m = some (i, d) ∧ d + w ≤ τ.lens.getD i 0 ∧
      (x.1 ≠ i ∨ d + w ≤ x.2.1 ∨ x.2.1 + x.2.2 ≤ d) := by
  unfold storeSlots at hx
  cases ha : addrOf τ m with
  | none => simp only [ha, Bool.false_eq_true, ite_false, List.not_mem_nil] at hx
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only [ha] at hx
    by_cases hw : d + w ≤ τ.lens.getD i 0
    · simp only [hw, ite_true, Bool.false_eq_true, ite_false, Bool.false_or, List.mem_filter,
        Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hx
      refine ⟨hx.1, i, d, rfl, hw, ?_⟩
      rcases hx.2 with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · simp only [hw, ite_false, Bool.false_eq_true, List.not_mem_nil] at hx

theorem mem_storeSlots_of_mem {σ : T} (m : MemOp) (w : Nat) {x : Nat × Nat × Nat} (hx : x ∈ σ.slots) :
    x ∈ storeSlots σ m w true := by
  unfold storeSlots
  cases ha : addrOf σ m with
  | none => simpa only [ite_true] using hx
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only
    by_cases hw : d + w ≤ σ.lens.getD i 0
    · simp only [hw, ite_true, Bool.true_or, List.filter_eq_self.mpr (fun _ _ => rfl), List.mem_cons]
      exact .inr hx
    · simpa only [hw, ite_false, ite_true] using hx

theorem mem_storeSlots_kept {σ : T} {m : MemOp} {w : Nat} {i d : Nat} (ha : addrOf σ m = some (i, d))
    (hw : d + w ≤ σ.lens.getD i 0) {x : Nat × Nat × Nat} (hx : x ∈ σ.slots)
    (ho : x.1 ≠ i ∨ d + w ≤ x.2.1 ∨ x.2.1 + x.2.2 ≤ d) (q : Bool) : x ∈ storeSlots σ m w q := by
  cases q
  · unfold storeSlots
    simp only [ha, hw, ite_true, Bool.false_eq_true, ite_false, Bool.false_or, List.mem_filter,
      Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    refine ⟨hx, ?_⟩
    rcases ho with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h
  · exact mem_storeSlots_of_mem m w hx

theorem mem_storeSlots_new {σ : T} {m : MemOp} {w : Nat} {i d : Nat} (ha : addrOf σ m = some (i, d))
    (hw : d + w ≤ σ.lens.getD i 0) : (i, d, w) ∈ storeSlots σ m w true := by
  unfold storeSlots
  simp only [ha, hw, ite_true, List.mem_cons, true_or]

theorem storeSlots_upd (hsl : ∀ x ∈ τ.slots, x ∈ sl) (m : MemOp) (w : Nat) {p q : Bool}
    (hpq : p = true → q = true) : ∀ x ∈ storeSlots τ m w p, x ∈ storeSlots (upd τ r f sl) m w q := by
  intro x hx
  cases p
  · obtain ⟨hs, i, d, ha, hw, ho⟩ := mem_storeSlots_false hx
    exact mem_storeSlots_kept (σ := upd τ r f sl) ha hw (hsl x hs) ho q
  · cases hpq rfl
    rcases mem_storeSlots_true hx with hs | ⟨i, d, ha, hw, rfl⟩
    · exact mem_storeSlots_of_mem (σ := upd τ r f sl) m w (hsl x hs)
    · exact mem_storeSlots_new (σ := upd τ r f sl) ha hw

theorem storeStep_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) (m : MemOp) (w : Nat) {p q : Bool} (hpq : p = true → q = true)
    (nb : List Nat) {τ' : T} (hs : storeStep τ m w p nb = some τ') :
    ∃ σ', storeStep (upd τ r f sl) m w q nb = some σ' ∧ LeR τ' σ' := by
  unfold storeStep at hs ⊢
  split at hs <;> [rename_i hm; cases hs]
  cases hs
  rw [ite_t (show memPub (upd τ r f sl) m = true from pub_upd hr hm)]
  exact ⟨_, rfl, ⟨hr, hf, storeSlots_upd hsl m w hpq, rfl⟩⟩

theorem leR_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) : LeR τ (upd τ r f sl) := ⟨hr, hf, hsl, rfl⟩

theorem step_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) (i : Instr) {τ' : T} (hs : step τ i = some τ') :
    ∃ σ', step (upd τ r f sl) i = some σ' ∧ LeR τ' σ' := by
  cases i with
  | mov d src =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hok
    rw [ite_t (by simp only [Bool.and_eq_true]; exact ⟨hok.1, srcOk_upd hr hok.2⟩)]
    refine ⟨_, rfl, ⟨set_upd hr d fun hp => ?_, hf, hsl, rfl⟩⟩
    simp only [Bool.or_eq_true] at hp ⊢
    exact hp.imp (srcPub_upd hr) (loadPub_upd hsl)
  | store m x => exact storeStep_upd hr hf hsl m 4 (pub_upd hr) _ hs
  | store8 m x => exact storeStep_upd hr hf hsl m 1 (pub_upd hr) _ hs
  | alu op d src =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hok
    rw [ite_t (by simp only [Bool.and_eq_true]; exact ⟨hok.1, srcOk_upd hr hok.2⟩)]
    have hp : (pub τ d && srcPub τ src && (!usesCarry op || τ.flags)) = true →
        (pub (upd τ r f sl) d && srcPub (upd τ r f sl) src && (!usesCarry op || f)) = true := fun hp => by
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp ⊢
      exact ⟨⟨pub_upd hr hp.1.1, srcPub_upd hr hp.1.2⟩, hp.2.imp id hf⟩
    refine ⟨_, rfl, ⟨?_, hp, hsl, rfl⟩⟩
    cases writes op
    · exact hr
    · exact set_upd hr d hp
  | shift _ d _ =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t hok]
    refine ⟨_, rfl, ⟨hr, fun hp => ?_, hsl, rfl⟩⟩
    simp only [Bool.and_eq_true] at hp ⊢
    exact ⟨hf hp.1, pub_upd hr hp.2⟩
  | bswap d =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t hok]
    exact ⟨_, rfl, ⟨hr, hf, hsl, rfl⟩⟩
  | movzx8 d m =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hok
    rw [ite_t (by simp only [Bool.and_eq_true]; exact ⟨hok.1, pub_upd hr hok.2⟩)]
    exact ⟨_, rfl, ⟨set_upd hr d id, hf, hsl, rfl⟩⟩
  | mul x =>
    simp only [step, Option.some.injEq, mulStep] at hs ⊢
    cases hs
    have hp : (pub τ .eax && pub τ x) = true →
        (pub (upd τ r f sl) .eax && pub (upd τ r f sl) x) = true := fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨pub_upd hr hp.1, pub_upd hr hp.2⟩
    refine ⟨_, rfl, ⟨?_, hp, hsl, rfl⟩⟩
    cases e : (pub τ .eax && pub τ x) <;> cases e' : (pub (upd τ r f sl) .eax && pub (upd τ r f sl) x) <;>
      simp only [Bool.false_eq_true, ite_true, ite_false]
    · exact RegSet.erase_mono (RegSet.erase_mono hr _) _
    · exact RegSet.subset_trans (RegSet.erase_subset _ _) (RegSet.subset_trans
        (RegSet.erase_subset _ _) (RegSet.subset_trans hr (RegSet.subset_trans
        (RegSet.subset_insert _ _) (RegSet.subset_insert _ _))))
    · exact absurd (hp e) (by rw [e']; exact Bool.false_ne_true)
    · exact RegSet.insert_mono (RegSet.insert_mono hr _) _
  | push _ => simp only [step, reduceCtorEq] at hs
  | pop _ _ => simp only [step, reduceCtorEq] at hs
  | alloc _ => simp only [step, reduceCtorEq] at hs
  | free _ => simp only [step, reduceCtorEq] at hs
  | movdquLoad _ _ => simp only [step, reduceCtorEq] at hs
  | movdquStore _ _ => simp only [step, reduceCtorEq] at hs
  | movqLoad _ _ => simp only [step, reduceCtorEq] at hs
  | movqStore _ _ => simp only [step, reduceCtorEq] at hs
  | mop _ => simp only [step, reduceCtorEq] at hs
  | mmxStore _ _ => simp only [step, reduceCtorEq] at hs
  | mmxEnter => simp only [step, reduceCtorEq] at hs
  | emms => simp only [step, reduceCtorEq] at hs
  | xop _ => simp only [step, reduceCtorEq] at hs

theorem LeR.sim {a a' b b' : T} (ha : Sim a' a) (hb : Sim b' b) (h : LeR a b) : LeR a' b' where
  regs := by rw [ha.regs, hb.regs]; exact h.regs
  flags e := by rw [hb.flags]; exact h.flags (ha.flags ▸ e)
  slots x hx := (hb.slots x).mpr (h.slots x ((ha.slots x).mp hx))
  shape := by
    have e := h.shape
    have e₁ : b.lens = a.lens := (congrArg T.lens e).trans rfl
    have e₂ : b.bases = a.bases := (congrArg T.bases e).trans rfl
    have e₃ : b.wbases = a.wbases := (congrArg T.wbases e).trans rfl
    have e₄ : b.argLen = a.argLen := (congrArg T.argLen e).trans rfl
    have e₅ : b.argBases = a.argBases := (congrArg T.argBases e).trans rfl
    have e₆ : b.stk = a.stk := (congrArg T.stk e).trans rfl
    have e₇ : b.room = a.room := (congrArg T.room e).trans rfl
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := a'
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := b'
    simp only [upd, T.mk.injEq, true_and]
    exact ⟨hb.lens.trans (e₁.trans ha.lens.symm), hb.bases.trans (e₂.trans ha.bases.symm),
      hb.wbases.trans (e₃.trans ha.wbases.symm), hb.argLen.trans (e₄.trans ha.argLen.symm),
      hb.argBases.trans (e₅.trans ha.argBases.symm), hb.stk.trans (e₆.trans ha.stk.symm),
      hb.room.trans (e₇.trans ha.room.symm)⟩

theorem LeR.step {τ σ τ' : T} (h : LeR τ σ) (i : Instr) (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ LeR τ' σ' := by
  rw [h.shape]; exact step_upd h.regs h.flags h.slots i hs

theorem callStep_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) {τ' : T} (hs : callStep τ = some τ') :
    ∃ σ', callStep (upd τ r f sl) = some σ' ∧ LeR τ' σ' := by
  unfold callStep at hs ⊢
  split at hs <;> [rename_i hok; cases hs]
  cases hs
  simp only [Bool.and_eq_true] at hok
  rw [ite_t (by simp only [Bool.and_eq_true]; exact ⟨pub_upd hr hok.1, hok.2⟩)]
  exact ⟨_, rfl, ⟨hr, hf, hsl, rfl⟩⟩

theorem retStep_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) {τ' : T} (hs : retStep τ = some τ') :
    ∃ σ', retStep (upd τ r f sl) = some σ' ∧ LeR τ' σ' := by
  unfold retStep at hs ⊢
  show ∃ σ', (match τ.stk with
    | none :: stk =>
      if pub (upd τ r f sl) .esp = true then
        some { upd τ r f sl with stk := stk, bases := kill τ .esp ++ stkBases stk } else none
    | _ => none) = some σ' ∧ _
  revert hs
  cases τ.stk with
  | nil => intro hs; cases hs
  | cons x stk =>
    cases x with
    | some _ => intro hs; cases hs
    | none =>
      intro hs
      simp only at hs ⊢
      split at hs <;> [rename_i hok; cases hs]
      cases hs
      rw [ite_t (pub_upd hr hok)]
      exact ⟨_, rfl, ⟨hr, hf, hsl, rfl⟩⟩

theorem pushSlots_upd (hr : τ.regs.subset r = true) :
    ∀ (rs : List Reg) (o : Nat), ∀ x ∈ pushSlots τ rs o, x ∈ pushSlots (upd τ r f sl) rs o := by
  intro rs
  induction rs with
  | nil => intro o x hx; cases hx
  | cons q rs ih =>
    intro o x hx
    simp only [pushSlots, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · left
      split at hx <;> [rename_i hp; cases hx]
      rw [ite_t (pub_upd hr hp)]; exact hx
    · exact .inr (ih _ x hx)

theorem pushWbases_upd (rs : List Reg) (o : Nat) :
    pushWbases (upd τ r f sl) rs o = pushWbases τ rs o := by
  induction rs generalizing o with
  | nil => rfl
  | cons q rs ih => simp only [pushWbases, ih]; rfl

theorem pushStep_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) (i : Instr) {τ' : T} (hs : pushStep τ i = some τ') :
    ∃ σ', pushStep (upd τ r f sl) i = some σ' ∧ LeR τ' σ' := by
  cases i with
  | push rs =>
    simp only [pushStep] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hok
    rw [ite_t (by simp only [Bool.and_eq_true]; exact ⟨⟨pub_upd hr hok.1.1, hok.1.2⟩, hok.2⟩)]
    refine ⟨_, rfl, ⟨hr, hf, fun x hx => ?_, ?_⟩⟩
    · simp only [pushed, List.mem_append, List.mem_map] at hx ⊢
      rcases hx with hx | ⟨y, hy, e⟩
      · exact .inl (pushSlots_upd hr rs _ x hx)
      · exact .inr ⟨y, hsl y hy, e⟩
    · have e := pushWbases_upd (τ := τ) (r := r) (f := f) (sl := sl) rs (4 * rs.length)
      simp only [pushed]
      rw [e]; rfl
  | _ => simp only [pushStep, reduceCtorEq] at hs

theorem popStep_upd (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) (i : Instr) {τ' : T} (hs : popStep τ i = some τ') :
    ∃ σ', popStep (upd τ r f sl) i = some σ' ∧ LeR τ' σ' := by
  cases i with
  | pop d k =>
    unfold popStep at hs ⊢
    show ∃ σ', (match τ.stk with
      | some _ :: stk =>
        if pub (upd τ r f sl) .esp = true then some _ else none
      | _ => none) = some σ' ∧ _
    revert hs
    cases τ.stk with
    | nil => intro hs; cases hs
    | cons x stk =>
      cases x with
      | none => intro hs; cases hs
      | some n =>
        intro hs
        simp only at hs ⊢
        split at hs <;> [rename_i hok; cases hs]
        cases hs
        rw [ite_t (pub_upd hr hok)]
        refine ⟨_, rfl, ⟨RegSet.erase_mono hr d, hf, fun x hx => ?_, rfl⟩⟩
        simp only [List.mem_map, List.mem_filter] at hx ⊢
        obtain ⟨y, ⟨hy, hy'⟩, e⟩ := hx
        exact ⟨y, ⟨hsl y hy, hy'⟩, e⟩
  | _ => simp only [popStep, reduceCtorEq] at hs

theorem mem_meet_slots {a b : T} {x : Nat × Nat × Nat} :
    x ∈ (meet a b).slots ↔ a.lens = b.lens ∧ x ∈ a.slots ∧ x ∈ b.slots := by
  simp only [meet]
  split
  · simp only [List.mem_filter, List.contains_iff_mem, true_and, *]
  · simp only [List.not_mem_nil, false_iff, not_and]; intro h; contradiction

theorem meet_upd {τ₁ τ₂ σ₁ σ₂ : T} (h₁ : LeR τ₁ σ₁) (h₂ : LeR τ₂ σ₂) : LeR (meet τ₁ τ₂) (meet σ₁ σ₂) := by
  obtain ⟨hr₁, hf₁, hs₁, e₁⟩ := h₁
  obtain ⟨hr₂, hf₂, hs₂, e₂⟩ := h₂
  generalize σ₁.regs = r₁, σ₁.flags = f₁, σ₁.slots = s₁ at *
  generalize σ₂.regs = r₂, σ₂.flags = f₂, σ₂.slots = s₂ at *
  subst e₁ e₂
  refine ⟨RegSet.inter_mono hr₁ hr₂, fun h => ?_, fun x hx => ?_, rfl⟩
  · simp only [meet, upd, Bool.and_eq_true] at h ⊢; exact ⟨hf₁ h.1, hf₂ h.2⟩
  · obtain ⟨hl, x₁, x₂⟩ := mem_meet_slots.mp hx
    exact mem_meet_slots.mpr ⟨hl, hs₁ x x₁, hs₂ x x₂⟩

end

/-! ## Frames: registers that code does not write -/

/-- What `Φ` says is public of the registers and flags, `σ` says too. -/
def frLe (Φ σ : T) : Bool := Φ.regs.subset σ.regs && (!Φ.flags || σ.flags)

theorem frLe_iff {Φ σ : T} : frLe Φ σ = true ↔ Φ.regs.subset σ.regs = true ∧ (Φ.flags = true → σ.flags = true) := by
  simp only [frLe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h₁, h₂⟩; exact ⟨h₁, fun h => h₂.elim (fun e => by rw [e] at h; cases h) id⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    cases e : Φ.flags
    · exact .inl rfl
    · exact .inr (h₂ e)

/-- The registers. -/
def allRegs : List Reg := [.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

/-- `i` writes no register of `F`, nor the flags if `F` has them. -/
def keepsI (F : T) (i : Instr) : Bool :=
  !F.flags && KList.all allRegs fun r => !F.regs.mem r || !clobbers i r

/-- `i` writes no register of index `j`. -/
def NoWrite (i : Instr) (j : Nat) : Prop := ∀ r, RegIdx.idx r = j → clobbers i r = false

theorem bit_set {τ : T} {d : Reg} {j : Nat} (h : RegIdx.idx d ≠ j) (hr : τ.regs.bits.testBit j = true)
    (p : Bool) : (set τ d p).bits.testBit j = true := by
  unfold set
  cases p
  · simp only [Bool.false_eq_true, ite_false, RegSet.erase_bits, Nat.testBit_xor, Nat.testBit_and,
      RegSet.testBit_bit, hr, h, decide_false, Bool.and_false, Bool.bne_false]
  · simp only [ite_true, RegSet.insert_bits, Nat.testBit_or, hr, Bool.true_or]

theorem bit_erase {s : RegSet Reg} {d : Reg} {j : Nat} (h : RegIdx.idx d ≠ j) (hr : s.bits.testBit j = true) :
    (s.erase d).bits.testBit j = true := by
  simp only [RegSet.erase_bits, Nat.testBit_xor, Nat.testBit_and, RegSet.testBit_bit, hr, h, decide_false,
    Bool.and_false, Bool.bne_false]

theorem bit_insert {s : RegSet Reg} (d : Reg) {j : Nat} (hr : s.bits.testBit j = true) :
    (s.insert d).bits.testBit j = true := by
  simp only [RegSet.insert_bits, Nat.testBit_or, hr, Bool.true_or]

theorem ne_of_dst {i : Instr} {d : Reg} {j : Nat} (hd : dst i = some d) (hc : NoWrite i j) :
    RegIdx.idx d ≠ j := by
  intro e
  have := hc d e
  cases i <;> simp_all [clobbers, dst]

theorem ne_of_clobbers {i : Instr} {d : Reg} {j : Nat} (hd : clobbers i d = true) (hc : NoWrite i j) :
    RegIdx.idx d ≠ j := by
  intro e; rw [hc d e] at hd; cases hd

theorem storeStep_regs {σ σ' : T} {m : MemOp} {w : Nat} {p : Bool} {nb : List Nat}
    (hs : storeStep σ m w p nb = some σ') : σ'.regs = σ.regs := by
  unfold storeStep at hs
  split at hs <;> [skip; cases hs]
  cases hs; rfl

/-- A step keeps public the registers the instruction does not write. -/
theorem step_bits {σ σ' : T} {i : Instr} (hs : step σ i = some σ') {j : Nat} (hc : NoWrite i j)
    (hr : σ.regs.bits.testBit j = true) : σ'.regs.bits.testBit j = true := by
  cases i
  case store | store8 => rw [storeStep_regs hs]; exact hr
  case push | pop | alloc | free | movdquLoad | movdquStore | movqLoad | movqStore | xop | mop | mmxStore | mmxEnter | emms => simp only [step, reduceCtorEq] at hs
  case mul q =>
    simp only [step, Option.some.injEq, mulStep] at hs
    subst hs
    have h₁ := ne_of_clobbers (d := .eax) (by simp [clobbers]) hc
    have h₂ := ne_of_clobbers (d := .edx) (by simp [clobbers]) hc
    split
    · exact bit_insert _ (bit_insert _ hr)
    · exact bit_erase h₂ (bit_erase h₁ hr)
  case alu op d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    simp only [Option.some.injEq] at hs
    subst hs
    show (if writes op = true then _ else σ.regs).bits.testBit j = true
    split
    · exact bit_set (ne_of_dst rfl hc) hr _
    · exact hr
  all_goals
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    simp only [Option.some.injEq] at hs; subst hs
    first | exact hr | exact bit_set (ne_of_dst rfl hc) hr _

theorem keepsI_spec {F Φ : T} {i : Instr} (hk : keepsI F i = true) (hΦF : frLe Φ F = true) :
    Φ.flags = false ∧ ∀ j, Φ.regs.bits.testBit j = true → NoWrite i j := by
  simp only [keepsI, Bool.and_eq_true, Bool.not_eq_true', KList.all_eq, List.all_eq_true, Bool.or_eq_true]
    at hk
  have hΦ := frLe_iff.mp hΦF
  refine ⟨?_, fun j hj r e => ?_⟩
  · cases e : Φ.flags
    · rfl
    · have := hΦ.2 e; rw [hk.1] at this; cases this
  · have hF : F.regs.mem r = true := RegSet.mem_iff.mpr (e ▸ RegSet.subset_iff.mp hΦ.1 j hj)
    have := hk.2 r (mem_allRegs r)
    rw [hF] at this
    exact this.resolve_left Bool.noConfusion

theorem step_keeps' {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true) (hΦF : frLe Φ F = true)
    (hΦ : frLe Φ σ = true) (hs : step σ i = some σ') : frLe Φ σ' = true := by
  obtain ⟨hf, hj⟩ := keepsI_spec hk hΦF
  refine frLe_iff.mpr ⟨RegSet.subset_iff.mpr fun j hb => ?_, fun h => by rw [hf] at h; cases h⟩
  exact step_bits hs (hj j hb) (RegSet.subset_iff.mp (frLe_iff.mp hΦ).1 j hb)

theorem pushStep_regs {σ σ' : T} {i : Instr} (hs : pushStep σ i = some σ') :
    σ'.regs = σ.regs ∧ σ'.flags = σ.flags := by
  cases i with
  | push rs =>
    simp only [pushStep] at hs
    split at hs <;> [skip; cases hs]
    cases hs; exact ⟨rfl, rfl⟩
  | _ => simp only [pushStep, reduceCtorEq] at hs

theorem popStep_regs {σ σ' : T} {d : Reg} {k : Nat} (hs : popStep σ (.pop d k) = some σ') :
    σ'.regs = σ.regs.erase d ∧ σ'.flags = σ.flags := by
  unfold popStep at hs
  revert hs
  cases σ.stk with
  | nil => intro hs; cases hs
  | cons x stk =>
    cases x with
    | none => intro hs; cases hs
    | some n =>
      intro hs
      simp only at hs
      split at hs <;> [skip; cases hs]
      cases hs; exact ⟨rfl, rfl⟩

theorem callStep_regs {σ σ' : T} (hs : callStep σ = some σ') : σ'.regs = σ.regs ∧ σ'.flags = σ.flags := by
  unfold callStep at hs; split at hs <;> [skip; cases hs]; cases hs; exact ⟨rfl, rfl⟩

theorem retStep_regs {σ σ' : T} (hs : retStep σ = some σ') : σ'.regs = σ.regs ∧ σ'.flags = σ.flags := by
  unfold retStep at hs
  split at hs
  · split at hs <;> [skip; cases hs]; cases hs; exact ⟨rfl, rfl⟩
  · cases hs

theorem le_join_frame {m Φ τ : T} (hm : le m τ = true) (hΦ : frLe Φ τ = true) :
    le { m with regs := m.regs.union Φ.regs, flags := m.flags || Φ.flags } τ = true := by
  obtain ⟨a₁, a₂⟩ := frLe_iff.mp hΦ
  unfold le at hm ⊢
  simp only [Bool.and_eq_true] at hm ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hw⟩, ha⟩, hab⟩, hk⟩, hro⟩ := hm
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨RegSet.union_subset hr a₁, ?_⟩, hl⟩, hb⟩, hs⟩, hw⟩, ha⟩, hab⟩, hk⟩, hro⟩
  cases ht : τ.flags
  · have hmf : m.flags = false := by
      cases e : m.flags
      · rfl
      · rw [e, ht] at hf; cases hf
    have hΦf : Φ.flags = false := by
      cases e : Φ.flags
      · rfl
      · have := a₂ e; rw [ht] at this; cases this
    rw [hmf, hΦf]; rfl
  · cases m.flags <;> cases Φ.flags <;> rfl

theorem frLe_meet {Φ a b : T} (h₁ : frLe Φ a = true) (h₂ : frLe Φ b = true) : frLe Φ (meet a b) = true := by
  obtain ⟨a₁, a₂⟩ := frLe_iff.mp h₁
  obtain ⟨b₁, b₂⟩ := frLe_iff.mp h₂
  refine frLe_iff.mpr ⟨RegSet.subset_inter a₁ b₁, fun h => ?_⟩
  show (a.flags && b.flags) = true
  rw [a₂ h, b₂ h]; rfl

end VG.X86.Taint

namespace VG.X86

open VG.X86.Taint in
/-- The x86 analysis is monotone along `LeR`, with frames of registers. -/
instance : VG.Taint.Frame taint where
  R := leR
  R_trans h₁ h₂ := leR_iff.mpr ((leR_iff.mp h₁).trans (leR_iff.mp h₂))
  R_right h := leR_iff.mpr (LeR.refl _)
  le_R hm h := by
    show leK _ _ = true
    rw [leK_eq]; exact le_of_le_leR (by rw [← leK_eq]; exact hm) (leR_iff.mp h)
  step {τ σ τ'} i h hs := by
    have hs : stepKD τ i = some τ' := hs
    rcases stepKD_spec τ i with ⟨h', -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h'] at hs; cases hs
    rw [h₁] at hs; cases hs
    obtain ⟨σ'', h₃, h₄⟩ := (leR_iff.mp h).step i h₂
    rcases stepKD_spec σ i with ⟨-, h'⟩ | ⟨c, d, h₅, h₆, hcd⟩
    · rw [h'] at h₃; cases h₃
    rw [h₆] at h₃; cases h₃
    exact ⟨c, h₅, leR_iff.mpr (h₄.sim hab hcd)⟩
  condPub _ h hc := (leR_iff.mp h).flags hc
  meet h₁ h₂ := leR_iff.mpr (meet_upd (leR_iff.mp h₁) (leR_iff.mp h₂))
  call {τ σ τ'} h hs := by
    have h := leR_iff.mp h
    have hs : callStep τ = some τ' := hs
    rw [h.shape]
    obtain ⟨σ', h₁, h₂⟩ := callStep_upd h.regs h.flags h.slots hs
    exact ⟨σ', h₁, leR_iff.mpr h₂⟩
  ret {τ σ τ'} h hs := by
    have h := leR_iff.mp h
    have hs : retStep τ = some τ' := hs
    rw [h.shape]
    obtain ⟨σ', h₁, h₂⟩ := retStep_upd h.regs h.flags h.slots hs
    exact ⟨σ', h₁, leR_iff.mpr h₂⟩
  push {τ σ τ'} i h hs := by
    have h := leR_iff.mp h
    have hs : pushStep τ i = some τ' := hs
    rw [h.shape]
    obtain ⟨σ', h₁, h₂⟩ := pushStep_upd h.regs h.flags h.slots i hs
    exact ⟨σ', h₁, leR_iff.mpr h₂⟩
  pop {τ σ τ'} i h hs := by
    have h := leR_iff.mp h
    have hs : popStep τ i = some τ' := hs
    rw [h.shape]
    obtain ⟨σ', h₁, h₂⟩ := popStep_upd h.regs h.flags h.slots i hs
    exact ⟨σ', h₁, leR_iff.mpr h₂⟩
  join m Φ := { m with regs := m.regs.union Φ.regs, flags := m.flags || Φ.flags }
  bot := { regs := .empty, flags := false }
  frameOf τ F := { regs := τ.regs.inter F.regs, flags := τ.flags && F.flags }
  Fr := frLe
  Fr_trans h₁ h₂ := by
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp h₁
    obtain ⟨b₁, b₂⟩ := frLe_iff.mp h₂
    exact frLe_iff.mpr ⟨RegSet.subset_trans a₁ b₁, fun h => b₂ (a₂ h)⟩
  Fr_R h₁ h₂ := by
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp h₁
    have h₂ := leR_iff.mp h₂
    exact frLe_iff.mpr ⟨RegSet.subset_trans a₁ h₂.regs, fun h => h₂.flags (a₂ h)⟩
  join_hint {m Φ τ} hm hΦ := by
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp hΦ
    refine ⟨?_, leR_iff.mpr ⟨RegSet.subset_union_left _ _, fun h => by simp [h], fun _ hx => hx, rfl⟩,
      frLe_iff.mpr ⟨RegSet.subset_union_right _ _, fun h => by simp [h]⟩⟩
    show leK _ _ = true
    rw [leK_eq]
    exact le_join_frame (by rw [← leK_eq]; exact hm) hΦ
  join_R {a b σ} ha hb := by
    have ha := leR_iff.mp ha
    obtain ⟨b₁, b₂⟩ := frLe_iff.mp hb
    refine leR_iff.mpr ⟨RegSet.union_subset ha.regs b₁, fun h => ?_, ha.slots, ?_⟩
    · simp only [Bool.or_eq_true] at h; exact h.elim ha.flags b₂
    · rw [ha.shape]; rfl
  frame_le_left _ _ := frLe_iff.mpr ⟨RegSet.inter_subset_left _ _, fun h => by
    simp only [Bool.and_eq_true] at h; exact h.1⟩
  frame_le_right _ _ _ := frLe_iff.mpr ⟨RegSet.inter_subset_right _ _, fun h => by
    simp only [Bool.and_eq_true] at h; exact h.2⟩
  frame_mono _ h := by
    have h := leR_iff.mp h
    refine frLe_iff.mpr ⟨RegSet.inter_mono h.regs (RegSet.subset_refl _), fun e => ?_⟩
    simp only [Bool.and_eq_true] at e ⊢; exact ⟨h.flags e.1, e.2⟩
  le_frame h₁ h₂ := by
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp h₁
    obtain ⟨b₁, b₂⟩ := frLe_iff.mp h₂
    exact frLe_iff.mpr ⟨RegSet.subset_inter a₁ b₁, fun h => by simp [a₂ h, b₂ h]⟩
  le_meet h₁ h₂ := frLe_meet h₁ h₂
  bot_le _ := frLe_iff.mpr ⟨RegSet.empty_subset _, fun h => by cases h⟩
  bot_valid := frLe_iff.mpr ⟨RegSet.empty_subset _, fun h => by cases h⟩
  keeps := keepsI
  keepsCall _ := true
  keeps_bot i := by
    simp only [keepsI, Bool.not_false, Bool.true_and, KList.all_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true']
    intro r _
    left; simp [RegSet.mem, RegSet.empty]
  keepsCall_bot := rfl
  step_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : stepKD σ i = some σ' := hs
    rcases stepKD_spec σ i with ⟨h', -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h'] at hs; cases hs
    rw [h₁] at hs; cases hs
    have h := frLe_iff.mp (step_keeps' i hk hΦF hΦ h₂)
    exact frLe_iff.mpr ⟨hab.regs ▸ h.1, fun e => hab.flags ▸ h.2 e⟩
  call_keeps _ _ hΦ hs := by
    obtain ⟨e₁, e₂⟩ := callStep_regs hs
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp hΦ
    exact frLe_iff.mpr ⟨e₁ ▸ a₁, fun h => e₂ ▸ a₂ h⟩
  ret_keeps _ _ hΦ hs := by
    obtain ⟨e₁, e₂⟩ := retStep_regs hs
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp hΦ
    exact frLe_iff.mpr ⟨e₁ ▸ a₁, fun h => e₂ ▸ a₂ h⟩
  push_keeps _ _ _ hΦ hs := by
    obtain ⟨e₁, e₂⟩ := pushStep_regs hs
    obtain ⟨a₁, a₂⟩ := frLe_iff.mp hΦ
    exact frLe_iff.mpr ⟨e₁ ▸ a₁, fun h => e₂ ▸ a₂ h⟩
  pop_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : popStep σ i = some σ' := hs
    cases i with
    | pop d k =>
      obtain ⟨e₁, e₂⟩ := popStep_regs hs
      obtain ⟨hf, hj⟩ := keepsI_spec hk hΦF
      obtain ⟨a₁, -⟩ := frLe_iff.mp hΦ
      refine frLe_iff.mpr ⟨RegSet.subset_iff.mpr fun j hb => ?_, fun h => by rw [hf] at h; cases h⟩
      rw [e₁]
      exact bit_erase (ne_of_dst rfl (hj j hb)) (RegSet.subset_iff.mp a₁ j hb)
    | _ => simp only [popStep, reduceCtorEq] at hs

instance : VG.Taint.CodeEq isa := ⟨@VG.Taint.codeBeq Instr Cond _ _⟩

end VG.X86
