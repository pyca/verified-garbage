module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.RegSetOrder

/-!
# Summaries for the PPC64LE analysis with public slots

`VG.PPC64LE.slotTaint` is not monotone along its order `le`: with more
region bases known, an access may find another base of its register first
(`addrOf`). It is monotone along a finer order, `LeR`: the same knowledge
about memory (the lengths and the bases), and more public registers and
slots. So summaries (`taint_summary`, `taint_decide_sum`) apply to code
whose taint knows the same about memory as the summary's, with more public
registers and slots; the hints of the checks still use `le`
(`Taint.Frame`, with `R := LeR`).

Summaries of this domain have no frames: `Fr Φ _` holds when `Φ` has no
public register, as `bot` has, and joining a frame adds nothing, so what a
summary ends with is its `post`.
-/

@[expose] public section

namespace VG.PPC64LE.SlotTaint

private theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

/-! ## The order -/

/-- `τ` and `σ` know the same about memory, and `σ` has at least the public
registers and slots of `τ`. -/
def leR (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && τ.slots.all (σ.slots.contains ·) && τ.lens == σ.lens &&
    decide (τ.bases = σ.bases)

/-- `τ` with the registers `r` and slots `sl`. -/
def upd (τ : T) (r : RegSet Reg) (sl : List (Nat × Nat × Nat)) : T :=
  { τ with regs := r, slots := sl }

/-- Every slot of `a` is one of `b`. -/
def Sub (a b : List (Nat × Nat × Nat)) : Prop := ∀ x ∈ a, x ∈ b

/-- `leR`, as a proposition. -/
structure LeR (τ σ : T) : Prop where
  regs : τ.regs.subset σ.regs = true
  slots : Sub τ.slots σ.slots
  shape : σ = upd τ σ.regs σ.slots

theorem leR_iff {τ σ : T} : leR τ σ = true ↔ LeR τ σ := by
  simp only [leR, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hr, hs⟩, hl⟩, hb⟩
    refine ⟨hr, hs, ?_⟩
    obtain ⟨_, _, _, _⟩ := σ
    simp only at hl hb
    simp only [upd, hl, hb]
  · rintro ⟨hr, hs, e⟩
    refine ⟨⟨⟨hr, hs⟩, ?_⟩, ?_⟩ <;> rw [e] <;> rfl

theorem LeR.refl (τ : T) : LeR τ τ := ⟨RegSet.subset_refl _, fun _ h => h, rfl⟩

theorem LeR.trans {a b c : T} (h₁ : LeR a b) (h₂ : LeR b c) : LeR a c where
  regs := RegSet.subset_trans h₁.regs h₂.regs
  slots x h := h₂.slots x (h₁.slots x h)
  shape := by rw [h₂.shape, h₁.shape]; rfl

theorem le_of_le_leR {m τ σ : T} (hm : le m τ = true) (h : LeR τ σ) : le m σ = true := by
  rw [h.shape]
  simp only [le, upd, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hm ⊢
  obtain ⟨⟨⟨hr, hl⟩, hb⟩, hs⟩ := hm
  exact ⟨⟨⟨RegSet.subset_trans hr h.regs, hl⟩, hb⟩, fun x hx => h.slots x (hs x hx)⟩

/-! ## Monotonicity -/

section
variable {τ : T} {r : RegSet Reg} {sl : List (Nat × Nat × Nat)}

theorem pub_upd (hr : τ.regs.subset r = true) {x : Reg} (h : pub τ x = true) :
    pub (upd τ r sl) x = true := RegSet.mem_of_subset hr h

theorem slotPub_upd (hsl : Sub τ.slots sl) {n : Reg} {off w : Nat} (h : slotPub τ n off w = true) :
    slotPub (upd τ r sl) n off w = true := by
  unfold slotPub at h ⊢
  rw [show addrOf (upd τ r sl) n off = addrOf τ n off from rfl]
  revert h
  cases addrOf τ n off with
  | none => intro h; cases h
  | some id =>
    intro h
    obtain ⟨i, d⟩ := id
    simp only [List.any_eq_true] at h ⊢
    obtain ⟨x, hx, e⟩ := h
    exact ⟨x, hsl x hx, e⟩

theorem set_upd (hr : τ.regs.subset r = true) (d : Reg) {p q : Bool} (hpq : p = true → q = true) :
    (set τ d p).subset (set (upd τ r sl) d q) = true := by
  unfold set
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono hr d
  · exact RegSet.subset_trans (RegSet.erase_subset τ.regs d)
      (RegSet.subset_trans hr (RegSet.subset_insert r d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono hr d

theorem storeSlots_upd (hsl : Sub τ.slots sl) (n : Reg) (off w : Nat) {p q : Bool}
    (hpq : p = true → q = true) : Sub (storeSlots τ n off w p) (storeSlots (upd τ r sl) n off w q) := by
  intro x hx
  unfold storeSlots at hx ⊢
  rw [show addrOf (upd τ r sl) n off = addrOf τ n off from rfl,
    show (upd τ r sl).lens = τ.lens from rfl, show (upd τ r sl).slots = sl from rfl]
  revert hx
  cases addrOf τ n off with
  | none =>
    intro hx
    cases p
    · simp at hx
    · simp only [ite_true] at hx; rw [hpq rfl]; exact hsl x hx
  | some id =>
    obtain ⟨i, d⟩ := id
    intro hx
    simp only at hx ⊢
    split
    · rename_i hw
      simp only [hw, ite_true] at hx
      cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.false_or,
        Bool.true_or, List.mem_cons, List.mem_filter, and_true] at hx ⊢
      · exact ⟨hsl x hx.1, hx.2⟩
      · exact .inr (hsl x hx.1)
      · exact absurd (hpq rfl) Bool.false_ne_true
      · exact hx.imp id (hsl x)
    · rename_i hw
      simp only [hw, ite_false] at hx
      cases p
      · simp at hx
      · simp only [ite_true] at hx; rw [hpq rfl]; simp only [ite_true]; exact hsl x hx

theorem storeStep_upd (hr : τ.regs.subset r = true) (hsl : Sub τ.slots sl) (n : Reg) (off w : Nat)
    {p q : Bool} (hpq : p = true → q = true) {τ' : T} (hs : storeStep τ n off w p = some τ') :
    ∃ σ', storeStep (upd τ r sl) n off w q = some σ' ∧ LeR τ' σ' := by
  unfold storeStep at hs ⊢
  split at hs <;> [rename_i hm; cases hs]
  cases hs
  rw [ite_t (pub_upd hr hm)]
  exact ⟨_, rfl, ⟨hr, storeSlots_upd hsl n off w hpq, rfl⟩⟩

theorem wr_upd (hr : τ.regs.subset r = true) (hsl : Sub τ.slots sl) (d : Reg) {p q : Bool}
    (hpq : p = true → q = true) : LeR (wr τ d p) (wr (upd τ r sl) d q) :=
  ⟨set_upd hr d hpq, hsl, rfl⟩

theorem and_upd (hr : τ.regs.subset r = true) {a b : Reg} (h : (pub τ a && pub τ b) = true) :
    (pub (upd τ r sl) a && pub (upd τ r sl) b) = true := by
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨pub_upd hr h.1, pub_upd hr h.2⟩

theorem step_upd (hr : τ.regs.subset r = true) (hsl : Sub τ.slots sl) (i : Instr) {τ' : T}
    (hs : step τ i = some τ') : ∃ σ', step (upd τ r sl) i = some σ' ∧ LeR τ' σ' := by
  have and_imp : ∀ {a b : Reg}, (pub τ a && pub τ b) = true → (pub (upd τ r sl) a && pub (upd τ r sl) b) = true :=
    and_upd hr
  cases i with
  | push | pop | alloc | free | adrSym | vop | lxvd2x | lxvd2xTbl | stxvd2x | mtvsrd | mfvsrd => simp only [step, reduceCtorEq] at hs
  | add d n m | sub d n m | mul d n m | mulhu d n m | addc d n m | subc d n m =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, wr_upd hr hsl d and_imp⟩
  | adde d n m | addze d n | sube d n m =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, wr_upd hr hsl d id⟩
  | logic op d n m =>
    simp only [step] at hs ⊢
    split at hs
    · rename_i hc
      rw [ite_t hc]
      cases hs
      exact ⟨_, rfl, ⟨set_upd hr d (pub_upd hr), hsl, rfl⟩⟩
    · rename_i hc
      rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]
      cases hs
      exact ⟨_, rfl, wr_upd hr hsl d and_imp⟩
  | addi d n imm | subi d n imm =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, ⟨set_upd hr d (pub_upd hr), hsl, rfl⟩⟩
  | ori d n _ | oris d n _ | rotr _ d n _ | lsr _ d n _ | lsl d n _ =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, wr_upd hr hsl d (pub_upd hr)⟩
  | li d _ | lis d _ | addSp d _ =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, wr_upd hr hsl d id⟩
  | mflr d =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, wr_upd hr hsl d id⟩
  | mtlr _ =>
    simp only [step, Option.some.injEq] at hs ⊢; subst hs
    exact ⟨_, rfl, ⟨hr, hsl, rfl⟩⟩
  | load sz t n off | lbz t n off =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    rw [ite_t (pub_upd hr hn)]
    exact ⟨_, rfl, wr_upd hr hsl t (slotPub_upd hsl)⟩
  | store sz t n off => exact storeStep_upd hr hsl n off _ (pub_upd hr) hs
  | stb t n off => exact storeStep_upd hr hsl n off 1 (pub_upd hr) hs
  | loadRev _ t a b =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    rw [ite_t (and_imp hn)]
    exact ⟨_, rfl, wr_upd hr hsl t id⟩
  | storeRev _ t a b =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    rw [ite_t (and_imp hn)]
    refine ⟨_, rfl, ⟨hr, ?_, rfl⟩⟩
    show Sub (if pub τ t then τ.slots else []) (if pub (upd τ r sl) t then sl else [])
    cases ht : pub τ t
    · intro x hx; simp at hx
    · rw [pub_upd hr ht]; exact hsl

theorem meet_upd {τ₁ τ₂ σ₁ σ₂ : T} (h₁ : LeR τ₁ σ₁) (h₂ : LeR τ₂ σ₂) : LeR (meet τ₁ τ₂) (meet σ₁ σ₂) := by
  rw [h₁.shape, h₂.shape]
  refine ⟨RegSet.inter_mono h₁.regs h₂.regs, ?_, rfl⟩
  intro x hx
  simp only [meet] at hx ⊢
  split at hx
  · rename_i he
    rw [ite_t (show (upd τ₁ σ₁.regs σ₁.slots).lens = (upd τ₂ σ₂.regs σ₂.slots).lens from he)]
    simp only [List.mem_filter, List.contains_iff_mem] at hx ⊢
    exact ⟨h₁.slots x hx.1, h₂.slots x hx.2⟩
  · simp at hx

theorem callStep_upd (hr : τ.regs.subset r = true) (hsl : Sub τ.slots sl) :
    LeR (callStep τ) (callStep (upd τ r sl)) :=
  ⟨RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono hr _) _) _, hsl, rfl⟩

end

/-- The only frame. -/
def botT : T := { regs := .empty }

end VG.PPC64LE.SlotTaint

namespace VG.PPC64LE

open VG.PPC64LE.SlotTaint in
/-- The PPC64LE analysis with public slots is monotone along `LeR`, with no
frames but `bot`. -/
instance : VG.Taint.Frame slotTaint where
  R := leR
  R_trans h₁ h₂ := leR_iff.mpr ((leR_iff.mp h₁).trans (leR_iff.mp h₂))
  R_right _ := leR_iff.mpr (LeR.refl _)
  le_R hm h := le_of_le_leR hm (leR_iff.mp h)
  step {τ σ τ'} i h hs := by
    have hs : step τ i = some τ' := stepK_eq ▸ hs
    have h := leR_iff.mp h
    show ∃ σ', stepK σ i = some σ' ∧ _
    rw [stepK_eq, h.shape]
    obtain ⟨σ', h₁, h₂⟩ := step_upd h.regs h.slots i hs
    exact ⟨σ', h₁, leR_iff.mpr h₂⟩
  condPub {τ σ} c h hc := by
    have h := leR_iff.mp h
    cases c <;> exact RegSet.mem_of_subset h.regs hc
  meet h₁ h₂ := leR_iff.mpr (meet_upd (leR_iff.mp h₁) (leR_iff.mp h₂))
  call {τ σ τ'} h hs := by
    have h := leR_iff.mp h
    cases hs
    rw [h.shape]
    exact ⟨_, rfl, leR_iff.mpr (callStep_upd h.regs h.slots)⟩
  ret {τ σ τ'} h hs := by
    cases hs
    exact ⟨σ, rfl, h⟩
  push _ _ hs := by cases hs
  pop _ _ hs := by cases hs
  join m _ := m
  bot := botT
  frameOf _ _ := botT
  Fr Φ _ := (SlotTaint.T.regs Φ).subset .empty
  Fr_trans h _ := h
  Fr_R h _ := h
  join_hint hm hΦ := ⟨hm, leR_iff.mpr (LeR.refl _), hΦ⟩
  join_R ha _ := ha
  frame_le_left _ _ := RegSet.subset_refl _
  frame_le_right _ _ _ := RegSet.subset_refl _
  frame_mono _ _ := RegSet.subset_refl _
  le_frame h _ := h
  le_meet h _ := h
  bot_le _ := RegSet.subset_refl _
  bot_valid := RegSet.subset_refl _
  keeps _ _ := true
  keepsCall _ := true
  keeps_bot _ := rfl
  keepsCall_bot := rfl
  step_keeps _ _ h _ _ := h
  call_keeps _ _ h _ := h
  ret_keeps _ _ h _ := h
  push_keeps _ _ _ h _ := h
  pop_keeps _ _ _ h _ := h

end VG.PPC64LE
