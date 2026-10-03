import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.RegSetOrder

/-!
# Summaries for the ARMv7 taint analysis

`taintS` is `Arm.taint` with an order (`leS`) for which the analysis is
monotone (`Taint.Frame`), so that its checks can use summaries of code they
contain (`taint_summary`, `taint_decide_sum`), as on x86-64
(`Proof/Framework/X86_64/TaintMono.lean`). It has the same taints and
agreement, so a check with it proves the same `ConstantTime`; its stores
add a public slot only if it is not there already (`stepKD`).

`Arm.taint`'s order is not monotone: a register may be known to hold the
base of several regions (`bases`), and an access through it uses the first;
with more known, another may come first. `leS` compares only taints whose
larger side has at most one region per register (`Fn`) and per stack
argument (`FnA`), which the analysis keeps. It also lets a taint that says
nothing about memory (no lengths and no slots) or about the stack arguments
be below any other, so that there is a least taint, `bot`.

A frame of a summary (what the summarized code does not write, `keeps`) is a
set of registers.
-/

namespace VG.Arm.Taint

open RegSet

private theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

/-! ## The order -/

/-- Each register holds the base of at most one known region. -/
def Fn (l : List (Reg × Nat)) : Prop := ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p = q

/-- Each stack argument holds the base of at most one known region. -/
def FnA (l : List (Nat × Nat)) : Prop := ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p = q

/-- `Fn`, for the kernel. -/
def fnK (l : List (Reg × Nat)) : Bool :=
  KList.all l fun p => KList.all l fun q => !regEq p.1 q.1 || Nat.beq p.2 q.2

/-- `FnA`, for the kernel. -/
def fnAK (l : List (Nat × Nat)) : Bool :=
  KList.all l fun p => KList.all l fun q => !Nat.beq p.1 q.1 || Nat.beq p.2 q.2

/-- `τ` says nothing more than `σ`, which has at most one base per register
and per stack argument. -/
def leS (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && (τ.lens == σ.lens || (τ.lens.isEmpty && τ.slots.isEmpty)) &&
    KList.all τ.bases (memB · σ.bases) && KList.all τ.slots (mem3 · σ.slots) &&
    (Nat.beq τ.argLen σ.argLen || (Nat.beq τ.argLen 0 && τ.argBases.isEmpty)) &&
    KList.all τ.argBases (mem2 · σ.argBases) && fnK σ.bases && fnAK σ.argBases

/-- `leS`, but for `Fn` and `FnA`. -/
structure LeW (τ σ : T) : Prop where
  regs : τ.regs.subset σ.regs = true
  flags : τ.flags = true → σ.flags = true
  lens : τ.lens = σ.lens ∨ (τ.lens = [] ∧ τ.slots = [])
  bases : ∀ p ∈ τ.bases, p ∈ σ.bases
  slots : ∀ p ∈ τ.slots, p ∈ σ.slots
  argLen : τ.argLen = σ.argLen ∨ (τ.argLen = 0 ∧ τ.argBases = [])
  argBases : ∀ p ∈ τ.argBases, p ∈ σ.argBases

/-- `leS`, as a proposition. -/
structure Le (τ σ : T) : Prop extends LeW τ σ where
  fn : Fn σ.bases
  fnA : FnA σ.argBases

theorem fnK_iff {l : List (Reg × Nat)} : fnK l = true ↔ Fn l := by
  simp only [fnK, KList.all_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    regEq_eq, KList.beq_eq, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Fn]
  constructor
  · intro h p hp q hq e
    rcases h p hp q hq with h | h
    · exact absurd e h
    · exact Prod.ext e h
  · intro h p hp q hq
    by_cases e : p.1 = q.1
    · have := h p hp q hq e; subst this; exact .inr rfl
    · exact .inl e

theorem fnAK_iff {l : List (Nat × Nat)} : fnAK l = true ↔ FnA l := by
  simp only [fnAK, KList.all_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    KList.beq_eq, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, FnA]
  constructor
  · intro h p hp q hq e
    rcases h p hp q hq with h | h
    · exact absurd e h
    · exact Prod.ext e h
  · intro h p hp q hq
    by_cases e : p.1 = q.1
    · have := h p hp q hq e; subst this; exact .inr rfl
    · exact .inl e

theorem leS_iff {τ σ : T} : leS τ σ = true ↔ Le τ σ := by
  simp only [leS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff,
    KList.all_eq, List.all_eq_true, memB_eq, mem3_eq, mem2_eq, List.contains_iff_mem, fnK_iff,
    fnAK_iff, KList.beq_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, ha⟩, hab⟩, hfn⟩, hfa⟩
    exact ⟨⟨hr, fun h => hf.elim (fun e => by rw [e] at h; cases h) id, hl, hb, hs, ha, hab⟩, hfn, hfa⟩
  · rintro ⟨⟨hr, hf, hl, hb, hs, ha, hab⟩, hfn, hfa⟩
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hr, ?_⟩, hl⟩, hb⟩, hs⟩, ha⟩, hab⟩, hfn⟩, hfa⟩
    cases e : τ.flags
    · exact .inl rfl
    · exact .inr (hf e)

/-! ### Soundness of the order -/

theorem LeW.wf {τ σ : T} {s : State} (hle : LeW τ σ) (h : Wf σ s) : Wf τ s where
  lens hne := by
    rcases hle.lens with e | ⟨e, -⟩
    · rw [e] at hne ⊢; exact h.lens hne
    · exact absurd e hne
  bases p hp := h.bases p (hle.bases p hp)
  args hp := by
    rcases hle.argLen with e | ⟨e, -⟩
    · rw [e] at hp ⊢; exact h.args hp
    · rw [e] at hp; cases hp
  argBases p hp := by
    rcases hle.argLen with e | ⟨-, e⟩
    · rw [e]; exact h.argBases p (hle.argBases p hp)
    · rw [e] at hp; cases hp

theorem leS_sound {τ σ : T} {s₁ s₂ : State} (hle : LeW τ σ) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ where
  rf := ⟨fun r h' => h.rf.1 r (RegSet.mem_of_subset hle.regs h'), fun hf => h.rf.2 (hle.flags hf)⟩
  wr hne := by
    rcases hle.lens with e | ⟨e, -⟩
    · rw [e] at hne; exact h.wr hne
    · exact absurd e hne
  wf₁ := hle.wf h.wf₁
  wf₂ := hle.wf h.wf₂
  ok sl hsl := by
    rcases hle.lens with e | ⟨-, e⟩
    · rw [e]; exact h.ok sl (hle.slots sl hsl)
    · rw [e] at hsl; cases hsl
  slots sl hsl := h.slots sl (hle.slots sl hsl)
  sp hp := by
    rcases hle.argLen with e | ⟨e, -⟩
    · rw [e] at hp; exact h.sp hp
    · rw [e] at hp; cases hp
  argMem k hk := by
    rcases hle.argLen with e | ⟨e, -⟩
    · rw [e] at hk; exact h.argMem k hk
    · rw [e] at hk; cases hk

/-! ### The order is a preorder -/

theorem Fn.sub {l l' : List (Reg × Nat)} (h : Fn l') (hs : ∀ p ∈ l, p ∈ l') : Fn l :=
  fun p hp q hq e => h p (hs p hp) q (hs q hq) e

theorem Fn.filter {l : List (Reg × Nat)} (h : Fn l) (P : Reg × Nat → Bool) : Fn (l.filter P) :=
  h.sub fun _ hp => (List.mem_filter.mp hp).1

theorem FnA.sub {l l' : List (Nat × Nat)} (h : FnA l') (hs : ∀ p ∈ l, p ∈ l') : FnA l :=
  fun p hp q hq e => h p (hs p hp) q (hs q hq) e

theorem LeW.refl (τ : T) : LeW τ τ :=
  ⟨RegSet.subset_refl _, id, .inl rfl, fun _ h => h, fun _ h => h, .inl rfl, fun _ h => h⟩

theorem Le.right {τ σ : T} (h : Le τ σ) : Le σ σ := ⟨LeW.refl σ, h.fn, h.fnA⟩

theorem nil_of_sub {α : Type} {l l' : List α} (h : ∀ x ∈ l, x ∈ l') (e : l' = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons x _ => have := h x (List.mem_cons_self ..); rw [e] at this; cases this

theorem LeW.trans {a b c : T} (h₁ : LeW a b) (h₂ : LeW b c) : LeW a c where
  regs := RegSet.subset_trans h₁.regs h₂.regs
  flags h := h₂.flags (h₁.flags h)
  lens := by
    rcases h₁.lens with e₁ | ⟨e₁, s₁⟩
    · rcases h₂.lens with e₂ | ⟨e₂, s₂⟩
      · exact .inl (e₁.trans e₂)
      · exact .inr ⟨e₁.trans e₂, nil_of_sub h₁.slots s₂⟩
    · exact .inr ⟨e₁, s₁⟩
  bases p hp := h₂.bases p (h₁.bases p hp)
  slots p hp := h₂.slots p (h₁.slots p hp)
  argLen := by
    rcases h₁.argLen with e₁ | ⟨e₁, s₁⟩
    · rcases h₂.argLen with e₂ | ⟨e₂, s₂⟩
      · exact .inl (e₁.trans e₂)
      · exact .inr ⟨e₁.trans e₂, nil_of_sub h₁.argBases s₂⟩
    · exact .inr ⟨e₁, s₁⟩
  argBases p hp := h₂.argBases p (h₁.argBases p hp)

theorem Le.trans {a b c : T} (h₁ : Le a b) (h₂ : Le b c) : Le a c := ⟨h₁.toLeW.trans h₂.toLeW, h₂.fn, h₂.fnA⟩

/-! ## Monotonicity of the steps -/

section
variable {τ σ : T}

theorem LeW.pubM (h : LeW τ σ) {r : Reg} (hr : pub τ r = true) : pub σ r = true :=
  RegSet.mem_of_subset h.regs hr

theorem LeW.op2PubM (h : LeW τ σ) {o : Op2} (hs : op2Pub τ o = true) : op2Pub σ o = true := by
  cases o <;> first | rfl | exact h.pubM hs

theorem find_mono {l l' : List (Reg × Nat)} (hs : ∀ p ∈ l, p ∈ l') (hf : Fn l') {b : Reg}
    {p : Reg × Nat} (h : l.find? (·.1 == b) = some p) : l'.find? (·.1 == b) = some p := by
  have hp := List.find?_some h
  have hm := hs p (List.mem_of_find?_eq_some h)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome (p := fun x : Reg × Nat => x.1 == b).mpr ⟨p, hm, hp⟩)
  rw [hq]
  have hq' := List.find?_some hq
  simp only [beq_iff_eq] at hp hq'
  exact congrArg some (hf q (List.mem_of_find?_eq_some hq) p hm (hq'.trans hp.symm))

theorem Le.addrOfM (h : Le τ σ) {n : Reg} {off : Nat} {x : Nat × Nat} (ha : addrOf τ n off = some x) :
    addrOf σ n off = some x := by
  unfold addrOf at ha ⊢
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ha
  rw [find_mono h.bases h.fn hp]; rfl

theorem Le.slotPubM (h : Le τ σ) {n : Reg} {off w : Nat} (hs : slotPub τ n off w = true) :
    slotPub σ n off w = true := by
  simp only [slotPub] at hs ⊢
  split at hs <;> rename_i x heq <;> [skip; cases hs]
  rw [h.addrOfM heq]
  obtain ⟨sl, hsl, hp⟩ := List.any_eq_true.mp hs
  exact List.any_eq_true.mpr ⟨sl, h.slots sl hsl, hp⟩

theorem set_mono (h : LeW τ σ) (d : Reg) {p q : Bool} (hpq : p = true → q = true) :
    (set τ d p).subset (set σ d q) = true := by
  unfold set
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono h.regs d
  · exact RegSet.subset_trans (RegSet.erase_subset τ.regs d)
      (RegSet.subset_trans h.regs (RegSet.subset_insert σ.regs d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono h.regs d

end

/-! ### Known bases -/

/-- The bases `a` are among `b`, which has at most one per register. -/
def BLe (a b : List (Reg × Nat)) : Prop := (∀ p ∈ a, p ∈ b) ∧ Fn b

theorem BLe.filter {a b : List (Reg × Nat)} (h : BLe a b) (P : Reg × Nat → Bool) :
    BLe (a.filter P) (b.filter P) :=
  ⟨fun p hp => List.mem_filter.mpr ⟨h.1 p (List.mem_filter.mp hp).1, (List.mem_filter.mp hp).2⟩,
    h.2.filter P⟩

/-- The bases after `d` gets the regions of the entries of a list `xs ⊆ ys`
that `ys` has at most one of. -/
theorem BLe.moved {α : Type} {a b : List (Reg × Nat)} (h : BLe a b) (d : Reg) {xs ys : List α}
    (hxy : ∀ x ∈ xs, x ∈ ys) (g : α → Nat) (hys : ∀ x ∈ ys, ∀ y ∈ ys, x = y ∨ g x = g y) :
    BLe (a.filter (·.1 != d) ++ xs.map fun x => (d, g x)) (b.filter (·.1 != d) ++ ys.map fun x => (d, g x)) := by
  refine ⟨fun p hp => ?_, fun p hp q hq e => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_append.mpr (.inl ((h.filter _).1 p hp))
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨x, hxy x hx, rfl⟩))
  · have hk : ∀ x ∈ b.filter (·.1 != d), x.1 ≠ d := fun x hx => by
      have := (List.mem_filter.mp hx).2
      simpa only [bne_iff_ne, ne_eq] using this
    rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
    · exact (h.2.filter _) p hp q hq e
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hq
      exact absurd e (hk p hp)
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
      exact absurd e.symm (hk q hq)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
      rcases hys x hx y hy with e | e
      · rw [e]
      · rw [e]

section
variable {τ σ : T}

theorem Le.bases' (h : Le τ σ) : BLe τ.bases σ.bases := ⟨h.bases, h.fn⟩

theorem Le.killM (h : Le τ σ) (d : Reg) : BLe (kill τ d) (kill σ d) := h.bases'.filter _

theorem Le.movBasesM (h : Le τ σ) (d : Reg) (o : Op2) : BLe (movBases τ d o) (movBases σ d o) := by
  cases o with
  | reg r =>
    refine h.bases'.moved d (fun x hx => ?_) Prod.snd fun x hx y hy => ?_
    · exact (h.bases'.filter (·.1 == r)).1 x hx
    · have hx' := List.mem_filter.mp hx
      have hy' := List.mem_filter.mp hy
      simp only [beq_iff_eq] at hx' hy'
      exact .inl (h.fn x hx'.1 y hy'.1 (hx'.2.trans hy'.2.symm))
  | _ => exact h.killM d

theorem Le.spBasesM (h : Le τ σ) (t : Reg) (off : Nat) : BLe (spBases τ t off) (spBases σ t off) := by
  refine h.bases'.moved t (fun x hx => ?_) Prod.snd fun x hx y hy => ?_
  · have hx' := List.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨h.argBases x hx'.1, hx'.2⟩
  · have hx' := List.mem_filter.mp hx
    have hy' := List.mem_filter.mp hy
    simp only [beq_iff_eq] at hx' hy'
    exact .inl (h.fnA x hx'.1 y hy'.1 (hx'.2.trans hy'.2.symm))

end

/-! ### Slots -/

theorem mem_storeSlots_true {τ : T} {n : Reg} {off w : Nat} {x : Nat × Nat × Nat}
    (hx : x ∈ storeSlots τ n off w true) :
    x ∈ τ.slots ∨ ∃ i d, addrOf τ n off = some (i, d) ∧ d + w ≤ τ.lens.getD i 0 ∧ x = (i, d, w) := by
  unfold storeSlots at hx
  cases ha : addrOf τ n off with
  | none => simp only [ha, ite_true] at hx; exact .inl hx
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only [ha] at hx
    by_cases hw : d + w ≤ τ.lens.getD i 0
    · simp only [hw, ite_true, Bool.true_or, List.filter_eq_self.mpr (fun _ _ => rfl),
        List.mem_cons] at hx
      exact hx.elim (fun e => .inr ⟨i, d, rfl, hw, e⟩) .inl
    · simp only [hw, ite_false, ite_true] at hx; exact .inl hx

theorem mem_storeSlots_false {τ : T} {n : Reg} {off w : Nat} {x : Nat × Nat × Nat}
    (hx : x ∈ storeSlots τ n off w false) :
    x ∈ τ.slots ∧ ∃ i d, addrOf τ n off = some (i, d) ∧ d + w ≤ τ.lens.getD i 0 ∧
      (x.1 ≠ i ∨ d + w ≤ x.2.1 ∨ x.2.1 + x.2.2 ≤ d) := by
  unfold storeSlots at hx
  cases ha : addrOf τ n off with
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

theorem mem_storeSlots_of_mem {σ : T} (n : Reg) (off w : Nat) {x : Nat × Nat × Nat} (hx : x ∈ σ.slots) :
    x ∈ storeSlots σ n off w true := by
  unfold storeSlots
  cases ha : addrOf σ n off with
  | none => simpa only [ite_true] using hx
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only
    by_cases hw : d + w ≤ σ.lens.getD i 0
    · simp only [hw, ite_true, Bool.true_or, List.filter_eq_self.mpr (fun _ _ => rfl), List.mem_cons]
      exact .inr hx
    · simpa only [hw, ite_false, ite_true] using hx

theorem mem_storeSlots_kept {σ : T} {n : Reg} {off w : Nat} {i d : Nat} (ha : addrOf σ n off = some (i, d))
    (hw : d + w ≤ σ.lens.getD i 0) {x : Nat × Nat × Nat} (hx : x ∈ σ.slots)
    (ho : x.1 ≠ i ∨ d + w ≤ x.2.1 ∨ x.2.1 + x.2.2 ≤ d) (q : Bool) : x ∈ storeSlots σ n off w q := by
  cases q
  · unfold storeSlots
    simp only [ha, hw, ite_true, Bool.false_eq_true, ite_false, Bool.false_or, List.mem_filter,
      Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    refine ⟨hx, ?_⟩
    rcases ho with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h
  · exact mem_storeSlots_of_mem n off w hx

theorem mem_storeSlots_new {σ : T} {n : Reg} {off w : Nat} {i d : Nat} (ha : addrOf σ n off = some (i, d))
    (hw : d + w ≤ σ.lens.getD i 0) : (i, d, w) ∈ storeSlots σ n off w true := by
  unfold storeSlots
  simp only [ha, hw, ite_true, List.mem_cons, true_or]

theorem storeSlots_mono {τ σ : T} (h : Le τ σ) (hl : τ.lens = σ.lens) (n : Reg) (off w : Nat)
    {p q : Bool} (hpq : p = true → q = true) :
    ∀ x ∈ storeSlots τ n off w p, x ∈ storeSlots σ n off w q := by
  intro x hx
  cases p
  · obtain ⟨hs, i, d, ha, hw, ho⟩ := mem_storeSlots_false hx
    exact mem_storeSlots_kept (h.addrOfM ha) (hl ▸ hw) (h.slots x hs) ho q
  · cases hpq rfl
    rcases mem_storeSlots_true hx with hs | ⟨i, d, ha, hw, rfl⟩
    · exact mem_storeSlots_of_mem n off w (h.slots x hs)
    · exact mem_storeSlots_new (h.addrOfM ha) (hl ▸ hw)

theorem storeSlots_bot {τ : T} (hl : τ.lens = []) (hs : τ.slots = []) (n : Reg) (off : Nat) {w : Nat}
    (hw : 0 < w) (p : Bool) : storeSlots τ n off w p = [] := by
  unfold storeSlots
  split
  · rw [hl, ite_f (by simp only [List.getD_nil]; omega)]
    cases p <;> simp [hs]
  · cases p <;> simp [hs]

/-! ### Steps -/

section
variable {τ σ : T}

theorem Le.upd (h : Le τ σ) {r₁ r₂ : RegSet Reg} (hr : r₁.subset r₂ = true) {f₁ f₂ : Bool}
    (hf : f₁ = true → f₂ = true) {b₁ b₂ : List (Reg × Nat)} (hb : BLe b₁ b₂) :
    Le { τ with regs := r₁, flags := f₁, bases := b₁ } { σ with regs := r₂, flags := f₂, bases := b₂ } :=
  ⟨⟨hr, hf, h.lens, hb.1, h.slots, h.argLen, h.argBases⟩, hb.2, h.fnA⟩

theorem Le.store (h : Le τ σ) (n : Reg) (off : Nat) {w : Nat} (hw : 0 < w) {p q : Bool}
    (hpq : p = true → q = true) {τ' : T} (hs : storeStep τ n off w p = some τ') :
    ∃ σ', storeStep σ n off w q = some σ' ∧ Le τ' σ' := by
  unfold storeStep at hs ⊢
  split at hs <;> [rename_i hm; cases hs]
  cases hs
  rw [ite_t (h.toLeW.pubM hm)]
  refine ⟨_, rfl, ⟨⟨h.regs, h.flags, ?_, h.bases, ?_, h.argLen, h.argBases⟩, h.fn, h.fnA⟩⟩
  · rcases h.lens with hl | ⟨hl, hsl⟩
    · exact .inl hl
    · exact .inr ⟨hl, storeSlots_bot hl hsl n off hw p⟩
  · rcases h.lens with hl | ⟨hl, hsl⟩
    · exact storeSlots_mono h hl n off w hpq
    · intro x hx; rw [storeSlots_bot hl hsl n off hw p] at hx; cases hx

theorem step_mono (h : Le τ σ) (i : Instr) {τ' : T} (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ Le τ' σ' := by
  have hw := h.toLeW
  have and2 : ∀ {a : Reg} {o : Op2}, (pub τ a && op2Pub τ o) = true → (pub σ a && op2Pub σ o) = true :=
    fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨hw.pubM hp.1, hw.op2PubM hp.2⟩
  cases i with
  | mov d o =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d hw.op2PubM) h.flags (h.movBasesM d o)⟩
  | dp _ d n o =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d and2) h.flags (h.killM d)⟩
  | adds d n o | subs d n o =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d and2) and2 (h.killM d)⟩
  | adc d n o =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    refine ⟨_, rfl, h.upd (set_mono hw d fun hp => ?_) h.flags (h.killM d)⟩
    simp only [Bool.and_eq_true] at hp ⊢
    exact ⟨⟨hw.pubM hp.1.1, hw.op2PubM hp.1.2⟩, h.flags hp.2⟩
  | cmp n o =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd h.regs and2 h.bases'⟩
  | movw d _ =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d id) h.flags (h.killM d)⟩
  | addSp d _ =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    refine ⟨_, rfl, h.upd (set_mono hw d fun hp => ?_) h.flags (h.killM d)⟩
    simp only [decide_eq_true_eq] at hp ⊢
    rcases h.argLen with e | ⟨e, -⟩
    · rw [← e]; exact hp
    · rw [e] at hp; cases hp
  | movt d _ =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d hw.pubM) h.flags (h.killM d)⟩
  | rev d m =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d hw.pubM) h.flags (h.killM d)⟩
  | mul d n m =>
    simp only [step, Option.some.injEq] at hs ⊢; cases hs
    refine ⟨_, rfl, h.upd (set_mono hw d fun hp => ?_) h.flags (h.killM d)⟩
    simp only [Bool.and_eq_true] at hp ⊢; exact ⟨hw.pubM hp.1, hw.pubM hp.2⟩
  | ldr t n off =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    rw [ite_t (hw.pubM hn)]
    exact ⟨_, rfl, h.upd (set_mono hw t h.slotPubM) h.flags (h.killM t)⟩
  | ldrb t n _ =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    rw [ite_t (hw.pubM hn)]
    exact ⟨_, rfl, h.upd (set_mono hw t id) h.flags (h.killM t)⟩
  | str t n off => exact h.store n off (by decide) hw.pubM hs
  | strb t n off => exact h.store n off (by decide) hw.pubM hs
  | ldrSp t off =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i ho; cases hs]
    cases hs
    have e : τ.argLen = σ.argLen := h.argLen.resolve_right fun hh => by rw [hh.1] at ho; omega
    rw [ite_t (e ▸ ho)]
    exact ⟨_, rfl, h.upd (set_mono hw t id) h.flags (h.spBasesM t off)⟩
  | push _ => simp only [step, reduceCtorEq] at hs
  | pop _ _ => simp only [step, reduceCtorEq] at hs
  | alloc _ => simp only [step, reduceCtorEq] at hs
  | free _ => simp only [step, reduceCtorEq] at hs

end

/-! ## Meets and joins -/

section
variable {a b c τ₁ τ₂ σ₁ σ₂ : T}

theorem mem_meet_bases {x : Reg × Nat} : x ∈ (meet a b).bases ↔ x ∈ a.bases ∧ x ∈ b.bases := by
  simp only [meet, List.mem_filter, List.contains_iff_mem]

theorem mem_meet_slots {x : Nat × Nat × Nat} :
    x ∈ (meet a b).slots ↔ a.lens = b.lens ∧ x ∈ a.slots ∧ x ∈ b.slots := by
  simp only [meet]
  split
  · simp only [List.mem_filter, List.contains_iff_mem, true_and, *]
  · simp only [List.not_mem_nil, false_iff, not_and]; intro h; contradiction

theorem mem_meet_argBases {x : Nat × Nat} :
    x ∈ (meet a b).argBases ↔ a.argLen = b.argLen ∧ x ∈ a.argBases ∧ x ∈ b.argBases := by
  simp only [meet]
  split
  · simp only [List.mem_filter, List.contains_iff_mem, true_and, *]
  · simp only [List.not_mem_nil, false_iff, not_and]; intro h; contradiction

theorem meet_lens : (meet a b).lens = if a.lens = b.lens then a.lens else [] := rfl

theorem meet_argLen : (meet a b).argLen = if a.argLen = b.argLen then a.argLen else 0 := rfl

theorem meet_bot (h : ¬a.lens = b.lens ∨ (a.slots = [] ∨ b.slots = []) ∧ a.lens = []) :
    (meet a b).lens = [] ∧ (meet a b).slots = [] := by
  refine ⟨?_, ?_⟩
  · rw [meet_lens]; split
    · rcases h with h | ⟨-, h⟩
      · contradiction
      · exact h
    · rfl
  · cases e : (meet a b).slots with
    | nil => rfl
    | cons x _ =>
      have hx := mem_meet_slots.mp (e ▸ List.mem_cons_self ..)
      rcases h with h | ⟨h | h, -⟩
      · exact absurd hx.1 h
      · rw [h] at hx; cases hx.2.1
      · rw [h] at hx; cases hx.2.2

theorem meet_argBot (h : ¬a.argLen = b.argLen ∨ (a.argBases = [] ∨ b.argBases = []) ∧ a.argLen = 0) :
    (meet a b).argLen = 0 ∧ (meet a b).argBases = [] := by
  refine ⟨?_, ?_⟩
  · rw [meet_argLen]; split
    · rcases h with h | ⟨-, h⟩
      · contradiction
      · exact h
    · rfl
  · cases e : (meet a b).argBases with
    | nil => rfl
    | cons x _ =>
      have hx := mem_meet_argBases.mp (e ▸ List.mem_cons_self ..)
      rcases h with h | ⟨h | h, -⟩
      · exact absurd hx.1 h
      · rw [h] at hx; cases hx.2.1
      · rw [h] at hx; cases hx.2.2

theorem LeW.meetM (h₁ : LeW τ₁ σ₁) (h₂ : LeW τ₂ σ₂) : LeW (meet τ₁ τ₂) (meet σ₁ σ₂) where
  regs := RegSet.inter_mono h₁.regs h₂.regs
  flags h := by
    simp only [meet, Bool.and_eq_true] at h ⊢; exact ⟨h₁.flags h.1, h₂.flags h.2⟩
  lens := by
    rcases h₁.lens with e₁ | ⟨e₁, s₁⟩
    · rcases h₂.lens with e₂ | ⟨e₂, s₂⟩
      · left; simp only [meet_lens, e₁, e₂]
      · by_cases e : τ₁.lens = τ₂.lens
        · exact .inr (meet_bot (.inr ⟨.inr s₂, e.trans e₂⟩))
        · exact .inr (meet_bot (.inl e))
    · exact .inr (meet_bot (by
        by_cases e : τ₁.lens = τ₂.lens
        · exact .inr ⟨.inl s₁, e₁⟩
        · exact .inl e))
  bases x hx := mem_meet_bases.mpr ⟨h₁.bases x (mem_meet_bases.mp hx).1, h₂.bases x (mem_meet_bases.mp hx).2⟩
  slots x hx := by
    obtain ⟨e, x₁, x₂⟩ := mem_meet_slots.mp hx
    refine mem_meet_slots.mpr ⟨?_, h₁.slots x x₁, h₂.slots x x₂⟩
    rcases h₁.lens with e₁ | ⟨-, s₁⟩
    · rcases h₂.lens with e₂ | ⟨-, s₂⟩
      · rw [← e₁, ← e₂, e]
      · rw [s₂] at x₂; cases x₂
    · rw [s₁] at x₁; cases x₁
  argLen := by
    rcases h₁.argLen with e₁ | ⟨e₁, s₁⟩
    · rcases h₂.argLen with e₂ | ⟨e₂, s₂⟩
      · left; simp only [meet_argLen, e₁, e₂]
      · by_cases e : τ₁.argLen = τ₂.argLen
        · exact .inr (meet_argBot (.inr ⟨.inr s₂, e.trans e₂⟩))
        · exact .inr (meet_argBot (.inl e))
    · exact .inr (meet_argBot (by
        by_cases e : τ₁.argLen = τ₂.argLen
        · exact .inr ⟨.inl s₁, e₁⟩
        · exact .inl e))
  argBases x hx := by
    obtain ⟨e, x₁, x₂⟩ := mem_meet_argBases.mp hx
    refine mem_meet_argBases.mpr ⟨?_, h₁.argBases x x₁, h₂.argBases x x₂⟩
    rcases h₁.argLen with e₁ | ⟨-, s₁⟩
    · rcases h₂.argLen with e₂ | ⟨-, s₂⟩
      · rw [← e₁, ← e₂, e]
      · rw [s₂] at x₂; cases x₂
    · rw [s₁] at x₁; cases x₁

theorem Le.meetM (h₁ : Le τ₁ σ₁) (h₂ : LeW τ₂ σ₂) : Le (meet τ₁ τ₂) (meet σ₁ σ₂) :=
  ⟨h₁.toLeW.meetM h₂, h₁.fn.sub fun _ hx => (mem_meet_bases.mp hx).1,
    h₁.fnA.sub fun _ hx => (mem_meet_argBases.mp hx).2.1⟩

theorem meet_le_left' (ha : Le a a) (b : T) : Le (meet a b) a := by
  refine ⟨⟨RegSet.inter_subset_left _ _, fun h => ?_, ?_, fun x hx => (mem_meet_bases.mp hx).1,
    fun x hx => (mem_meet_slots.mp hx).2.1, ?_, fun x hx => (mem_meet_argBases.mp hx).2.1⟩, ha.fn, ha.fnA⟩
  · simp only [meet, Bool.and_eq_true] at h; exact h.1
  · by_cases e : a.lens = b.lens
    · left; rw [meet_lens, ite_t e]
    · exact .inr (meet_bot (.inl e))
  · by_cases e : a.argLen = b.argLen
    · left; rw [meet_argLen, ite_t e]
    · exact .inr (meet_argBot (.inl e))

theorem meet_le_right' (a : T) (hb : Le b b) : Le (meet a b) b := by
  refine ⟨⟨RegSet.inter_subset_right _ _, fun h => ?_, ?_, fun x hx => (mem_meet_bases.mp hx).2,
    fun x hx => (mem_meet_slots.mp hx).2.2, ?_, fun x hx => (mem_meet_argBases.mp hx).2.2⟩, hb.fn, hb.fnA⟩
  · simp only [meet, Bool.and_eq_true] at h; exact h.2
  · by_cases e : a.lens = b.lens
    · left; rw [meet_lens, ite_t e, e]
    · exact .inr (meet_bot (.inl e))
  · by_cases e : a.argLen = b.argLen
    · left; rw [meet_argLen, ite_t e, e]
    · exact .inr (meet_argBot (.inl e))

theorem le_meet' (hb : Le a b) (hc : Le a c) : Le a (meet b c) := by
  refine ⟨⟨RegSet.subset_inter hb.regs hc.regs, fun h => ?_, ?_,
    fun x hx => mem_meet_bases.mpr ⟨hb.bases x hx, hc.bases x hx⟩, fun x hx => ?_, ?_, fun x hx => ?_⟩,
    hb.fn.sub fun _ hx => (mem_meet_bases.mp hx).1, hb.fnA.sub fun _ hx => (mem_meet_argBases.mp hx).2.1⟩
  · simp only [meet, Bool.and_eq_true]; exact ⟨hb.flags h, hc.flags h⟩
  · rcases hb.lens with e₁ | bot
    · rcases hc.lens with e₂ | bot
      · left; rw [meet_lens, ite_t (e₁.symm.trans e₂), e₁]
      · exact .inr bot
    · exact .inr bot
  · refine mem_meet_slots.mpr ⟨?_, hb.slots x hx, hc.slots x hx⟩
    rcases hb.lens with e₁ | ⟨-, s⟩
    · rcases hc.lens with e₂ | ⟨-, s⟩
      · exact e₁.symm.trans e₂
      · rw [s] at hx; cases hx
    · rw [s] at hx; cases hx
  · rcases hb.argLen with e₁ | bot
    · rcases hc.argLen with e₂ | bot
      · left; rw [meet_argLen, ite_t (e₁.symm.trans e₂), e₁]
      · exact .inr bot
    · exact .inr bot
  · refine mem_meet_argBases.mpr ⟨?_, hb.argBases x hx, hc.argBases x hx⟩
    rcases hb.argLen with e₁ | ⟨-, s⟩
    · rcases hc.argLen with e₂ | ⟨-, s⟩
      · exact e₁.symm.trans e₂
      · rw [s] at hx; cases hx
    · rw [s] at hx; cases hx

/-- The join: what either says is public. Its lengths are those of `a`, unless
`a` says nothing about memory, and so are its stack arguments. -/
def join (a b : T) : T where
  regs := a.regs.union b.regs
  flags := a.flags || b.flags
  lens := if a.lens.isEmpty && a.slots.isEmpty then b.lens else a.lens
  bases := a.bases ++ b.bases
  slots := a.slots ++ b.slots
  argLen := if a.argLen == 0 && a.argBases.isEmpty then b.argLen else a.argLen
  argBases := a.argBases ++ b.argBases

theorem join_lens (a b : T) :
    ((join a b).lens = b.lens ∧ a.lens = [] ∧ a.slots = []) ∨
      ((join a b).lens = a.lens ∧ ¬(a.lens = [] ∧ a.slots = [])) := by
  by_cases h : a.lens = [] ∧ a.slots = []
  · exact .inl ⟨by simp only [join, h, List.isEmpty_nil, Bool.and_self, ite_true], h⟩
  · refine .inr ⟨?_, h⟩
    have : (a.lens.isEmpty && a.slots.isEmpty) = false := by
      cases h1 : a.lens.isEmpty <;> cases h2 : a.slots.isEmpty <;> try rfl
      exact absurd ⟨List.isEmpty_iff.mp h1, List.isEmpty_iff.mp h2⟩ h
    simp only [join, this, Bool.false_eq_true, ite_false]

theorem join_argLen (a b : T) :
    ((join a b).argLen = b.argLen ∧ a.argLen = 0 ∧ a.argBases = []) ∨
      ((join a b).argLen = a.argLen ∧ ¬(a.argLen = 0 ∧ a.argBases = [])) := by
  by_cases h : a.argLen = 0 ∧ a.argBases = []
  · exact .inl ⟨by simp only [join, h, List.isEmpty_nil, Bool.and_true, beq_self_eq_true, ite_true], h⟩
  · refine .inr ⟨?_, h⟩
    have : (a.argLen == 0 && a.argBases.isEmpty) = false := by
      cases h1 : (a.argLen == 0) <;> cases h2 : a.argBases.isEmpty <;> try rfl
      exact absurd ⟨beq_iff_eq.mp h1, List.isEmpty_iff.mp h2⟩ h
    simp only [join, this, Bool.false_eq_true, ite_false]

theorem join_lub (ha : Le a c) (hb : Le b c) : Le a (join a b) ∧ Le b (join a b) ∧ Le (join a b) c := by
  have fnJ : Fn (join a b).bases := ha.fn.sub fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ha.bases x hx
    · exact hb.bases x hx
  have fnAJ : FnA (join a b).argBases := ha.fnA.sub fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ha.argBases x hx
    · exact hb.argBases x hx
  have sl : ∀ x ∈ (join a b).slots, x ∈ c.slots := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ha.slots x hx
    · exact hb.slots x hx
  have ab : ∀ x ∈ (join a b).argBases, x ∈ c.argBases := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ha.argBases x hx
    · exact hb.argBases x hx
  -- The lengths and the arguments.
  have hlA : a.lens = (join a b).lens ∨ (a.lens = [] ∧ a.slots = []) := by
    rcases join_lens a b with ⟨-, h⟩ | ⟨e, -⟩
    · exact .inr h
    · exact .inl e.symm
  have hlB : b.lens = (join a b).lens ∨ (b.lens = [] ∧ b.slots = []) := by
    rcases join_lens a b with ⟨e, -⟩ | ⟨e, hn⟩
    · exact .inl e.symm
    · rcases hb.lens with e' | bot
      · exact .inl (by rw [e, ha.lens.resolve_right hn, e'])
      · exact .inr bot
  have hlC : (join a b).lens = c.lens ∨ ((join a b).lens = [] ∧ (join a b).slots = []) := by
    rcases join_lens a b with ⟨e, -, hs⟩ | ⟨e, hn⟩
    · rcases hb.lens with e' | ⟨e', s'⟩
      · exact .inl (e.trans e')
      · exact .inr ⟨e.trans e', by simp only [join, hs, s', List.append_nil]⟩
    · exact .inl (e.trans (ha.lens.resolve_right hn))
  have haA : a.argLen = (join a b).argLen ∨ (a.argLen = 0 ∧ a.argBases = []) := by
    rcases join_argLen a b with ⟨-, h⟩ | ⟨e, -⟩
    · exact .inr h
    · exact .inl e.symm
  have haB : b.argLen = (join a b).argLen ∨ (b.argLen = 0 ∧ b.argBases = []) := by
    rcases join_argLen a b with ⟨e, -⟩ | ⟨e, hn⟩
    · exact .inl e.symm
    · rcases hb.argLen with e' | bot
      · exact .inl (by rw [e, ha.argLen.resolve_right hn, e'])
      · exact .inr bot
  have haC : (join a b).argLen = c.argLen ∨ ((join a b).argLen = 0 ∧ (join a b).argBases = []) := by
    rcases join_argLen a b with ⟨e, -, hs⟩ | ⟨e, hn⟩
    · rcases hb.argLen with e' | ⟨e', s'⟩
      · exact .inl (e.trans e')
      · exact .inr ⟨e.trans e', by simp only [join, hs, s', List.append_nil]⟩
    · exact .inl (e.trans (ha.argLen.resolve_right hn))
  refine ⟨⟨⟨RegSet.subset_union_left _ _, fun h => by simp only [join, h, Bool.true_or], hlA,
      fun x hx => List.mem_append.mpr (.inl hx), fun x hx => List.mem_append.mpr (.inl hx), haA,
      fun x hx => List.mem_append.mpr (.inl hx)⟩, fnJ, fnAJ⟩,
    ⟨⟨RegSet.subset_union_right _ _, fun h => by simp only [join, h, Bool.or_true], hlB,
      fun x hx => List.mem_append.mpr (.inr hx), fun x hx => List.mem_append.mpr (.inr hx), haB,
      fun x hx => List.mem_append.mpr (.inr hx)⟩, fnJ, fnAJ⟩,
    ⟨⟨RegSet.union_subset ha.regs hb.regs, fun h => ?_, hlC, fun x hx => ?_, sl, haC, ab⟩,
      hb.fn, hb.fnA⟩⟩
  · simp only [join, Bool.or_eq_true] at h; exact h.elim ha.flags hb.flags
  · rcases List.mem_append.mp hx with hx | hx
    · exact ha.bases x hx
    · exact hb.bases x hx

/-- Nothing is public. -/
def bot : T := { regs := .empty, flags := false }

theorem bot_le' (ha : Le a a) : Le bot a :=
  ⟨⟨RegSet.empty_subset _, (fun h => by cases h), .inr ⟨rfl, rfl⟩, (fun _ h => by cases h),
    (fun _ h => by cases h), .inr ⟨rfl, rfl⟩, (fun _ h => by cases h)⟩, ha.fn, ha.fnA⟩

theorem bot_valid' : Le bot bot := bot_le' ⟨LeW.refl _, (fun _ h => by cases h), (fun _ h => by cases h)⟩

end

/-! ## Frames: registers that code does not write -/

/-- `F` says only that registers are public. -/
def regOnly (F : T) : Bool :=
  !F.flags && F.lens.isEmpty && F.bases.isEmpty && F.slots.isEmpty && Nat.beq F.argLen 0 &&
    F.argBases.isEmpty

/-- `i` writes no register of `F`, which says only that registers are public. -/
def keepsI (F : T) (i : Instr) : Bool :=
  regOnly F && match dst i with
    | some d => !F.regs.mem d
    | none => true

/-- A call writes `lr` and `r12`. -/
def keepsCallI (F : T) : Bool := regOnly F && !F.regs.mem .lr && !F.regs.mem .r12

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

theorem storeStep_regs {σ σ' : T} {n : Reg} {off w : Nat} {p : Bool} (hs : storeStep σ n off w p = some σ') :
    σ'.regs = σ.regs := by
  unfold storeStep at hs
  split at hs <;> [skip; cases hs]
  cases hs; rfl

/-- A step keeps public the registers the instruction does not write. -/
theorem step_bits {σ σ' : T} {i : Instr} (hs : step σ i = some σ') {j : Nat}
    (hc : ∀ d, dst i = some d → RegIdx.idx d ≠ j) (hr : σ.regs.bits.testBit j = true) :
    σ'.regs.bits.testBit j = true := by
  cases i
  case str | strb => rw [storeStep_regs hs]; exact hr
  case push | pop | alloc | free => simp only [step, reduceCtorEq] at hs
  case cmp => simp only [step, Option.some.injEq] at hs; subst hs; exact hr
  all_goals
    simp only [step] at hs
    first
    | (simp only [Option.some.injEq] at hs; subst hs; exact bit_set (hc _ rfl) hr _)
    | (split at hs <;> [skip; cases hs]
       simp only [Option.some.injEq] at hs; subst hs
       exact bit_set (hc _ rfl) hr _)

section
variable {F Φ σ σ' : T}

theorem regOnly_spec (hk : regOnly F = true) :
    F.flags = false ∧ F.lens = [] ∧ F.bases = [] ∧ F.slots = [] ∧ F.argLen = 0 ∧ F.argBases = [] := by
  simp only [regOnly, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, KList.beq_eq,
    beq_iff_eq] at hk
  obtain ⟨⟨⟨⟨⟨hf, hl⟩, hb⟩, hs⟩, ha⟩, hab⟩ := hk
  exact ⟨hf, hl, hb, hs, ha, hab⟩

/-- What a frame keeps public, if `Φ` (below `F`) has the registers. -/
theorem le_of_frame (hk : regOnly F = true) (hΦF : Le Φ F) (hr : Φ.regs.subset σ.regs = true)
    (hfn : Fn σ.bases) (hfa : FnA σ.argBases) : Le Φ σ := by
  obtain ⟨hf, hl, hb, hs, ha, hab⟩ := regOnly_spec hk
  have hs' : Φ.slots = [] := nil_of_sub hΦF.slots hs
  have hab' : Φ.argBases = [] := nil_of_sub hΦF.argBases hab
  refine ⟨⟨hr, (fun h => by have := hΦF.flags h; rw [hf] at this; cases this), ?_, fun x hx => ?_,
    (fun x hx => by rw [hs'] at hx; cases hx), ?_, (fun x hx => by rw [hab'] at hx; cases hx)⟩, hfn, hfa⟩
  · rcases hΦF.lens with e | bot
    · exact .inr ⟨e.trans hl, hs'⟩
    · exact .inr bot
  · have := hΦF.bases x hx; rw [hb] at this; cases this
  · rcases hΦF.argLen with e | bot
    · exact .inr ⟨e.trans ha, hab'⟩
    · exact .inr bot

theorem step_keeps' (i : Instr) (hk : keepsI F i = true) (hΦF : Le Φ F) (hΦ : Le Φ σ)
    (hs : step σ i = some σ') : Le Φ σ' := by
  simp only [keepsI, Bool.and_eq_true] at hk
  obtain ⟨σ'', hs', hle⟩ := step_mono hΦ.right i hs
  rw [hs] at hs'; cases hs'
  refine le_of_frame hk.1 hΦF (RegSet.subset_iff.mpr fun j hj => ?_) hle.fn hle.fnA
  refine step_bits hs (fun d hd e => ?_) (RegSet.subset_iff.mp hΦ.regs j hj)
  have hF : F.regs.mem d = true := RegSet.mem_iff.mpr (e ▸ RegSet.subset_iff.mp hΦF.regs j hj)
  have := hk.2
  rw [hd] at this
  simp only [hF, Bool.not_true, Bool.false_eq_true] at this

end

/-! ## Stores of public values, without repeats -/

/-- The slots after a store, without adding one that is there. -/
def storeSlotsKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOfK τ n off with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      let kept := KList.filter (fun sl => p || !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
        Nat.ble (sl.2.1 + sl.2.2) d) τ.slots
      bif p then (bif mem3 (i, d, w) kept then kept else (i, d, w) :: kept) else kept
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

def storeStepKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  bif pub τ n then some { τ with slots := storeSlotsKD τ n off w p } else none

/-- `stepK`, with stores that do not repeat a slot (written out, rather than
calling `stepK`, so that the kernel matches on the instruction once). -/
def stepKD (τ : T) : Instr → Option T
  | .mov d op2 => some { τ with regs := setK τ d (op2Pub τ op2), bases := movBasesK τ d op2 }
  | .dp _ d n op2 => some { τ with regs := setK τ d (pub τ n && op2Pub τ op2), bases := killK τ d }
  | .adds d n op2 | .subs d n op2 =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := setK τ d p, flags := p, bases := killK τ d }
  | .adc d n op2 =>
    some { τ with regs := setK τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := killK τ d }
  | .cmp n op2 => some { τ with flags := pub τ n && op2Pub τ op2 }
  | .movw d _ => some { τ with regs := setK τ d true, bases := killK τ d }
  | .addSp d _ => some { τ with regs := setK τ d (decide (0 < τ.argLen)), bases := killK τ d }
  | .movt d _ => some { τ with regs := setK τ d (pub τ d), bases := killK τ d }
  | .rev d m => some { τ with regs := setK τ d (pub τ m), bases := killK τ d }
  | .mul d n m => some { τ with regs := setK τ d (pub τ n && pub τ m), bases := killK τ d }
  | .ldr t n off =>
    bif pub τ n then some { τ with regs := setK τ t (slotPubK τ n off 4), bases := killK τ t } else none
  | .str t n off => storeStepKD τ n off 4 (pub τ t)
  | .ldrb t n _ => bif pub τ n then some { τ with regs := setK τ t false, bases := killK τ t } else none
  | .strb t n off => storeStepKD τ n off 1 (pub τ t)
  | .ldrSp t off =>
    bif Nat.ble (off + 4) τ.argLen then some { τ with regs := setK τ t true, bases := spBasesK τ t off }
    else none
  | .push _ | .pop .. | .alloc _ | .free _ => none

/-- The same taints, but for repeated slots. -/
structure Sim (a b : T) : Prop where
  regs : a.regs = b.regs
  flags : a.flags = b.flags
  lens : a.lens = b.lens
  bases : a.bases = b.bases
  slots : ∀ x, x ∈ a.slots ↔ x ∈ b.slots
  argLen : a.argLen = b.argLen
  argBases : a.argBases = b.argBases

theorem Sim.refl (a : T) : Sim a a := ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl, rfl, rfl⟩

theorem Le.sim {a a' b b' : T} (ha : Sim a' a) (hb : Sim b' b) (h : Le a b) : Le a' b' := by
  refine ⟨⟨(by rw [ha.regs, hb.regs]; exact h.regs), (fun e => by rw [hb.flags]; exact h.flags (ha.flags ▸ e)),
    ?_, (fun x hx => by rw [hb.bases]; exact h.bases x (ha.bases ▸ hx)),
    fun x hx => (hb.slots x).mpr (h.slots x ((ha.slots x).mp hx)),
    (by rw [ha.argLen, hb.argLen, ha.argBases]; exact h.argLen),
    (fun x hx => by rw [hb.argBases]; exact h.argBases x (ha.argBases ▸ hx))⟩,
    (by rw [hb.bases]; exact h.fn), (by rw [hb.argBases]; exact h.fnA)⟩
  rcases h.lens with e | ⟨e, es⟩
  · exact .inl (by rw [ha.lens, hb.lens, e])
  · exact .inr ⟨by rw [ha.lens, e], nil_of_sub (fun x hx => (ha.slots x).mp hx) es⟩

theorem Sim.agree {a b : T} {s₁ s₂ : State} (h : Sim a b) (hb : Agree b s₁ s₂) : Agree a s₁ s₂ :=
  leS_sound ⟨(by rw [h.regs]; exact RegSet.subset_refl _), (fun e => h.flags ▸ e), .inl h.lens,
    fun x hx => h.bases ▸ hx, fun x hx => (h.slots x).mp hx, .inl h.argLen, fun x hx => h.argBases ▸ hx⟩ hb

theorem mem_storeSlotsKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) (x : Nat × Nat × Nat) :
    x ∈ storeSlotsKD τ n off w p ↔ x ∈ storeSlots τ n off w p := by
  rw [← storeSlotsK_eq]
  unfold storeSlotsKD storeSlotsK
  cases addrOfK τ n off with
  | none => exact Iff.rfl
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only
    cases Nat.ble (d + w) (τ.lens.getD i 0) <;> cases p <;> simp only [Bool.cond_false, Bool.cond_true]
    generalize KList.filter _ τ.slots = l
    cases hm : mem3 (i, d, w) l
    · exact Iff.rfl
    · rw [mem3_eq, List.contains_iff_mem] at hm
      simp only [Bool.cond_true, List.mem_cons, iff_or_self]
      rintro rfl; exact hm

theorem stepKD_spec (τ : T) (i : Instr) :
    (stepKD τ i = none ∧ step τ i = none) ∨ ∃ a b, stepKD τ i = some a ∧ step τ i = some b ∧ Sim a b := by
  have st : ∀ n off w p, (storeStepKD τ n off w p = none ∧ storeStep τ n off w p = none) ∨
      ∃ a b, storeStepKD τ n off w p = some a ∧ storeStep τ n off w p = some b ∧ Sim a b := by
    intro n off w p
    unfold storeStepKD storeStep
    cases pub τ n
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨_, _, rfl, rfl, ⟨rfl, rfl, rfl, rfl, mem_storeSlotsKD τ n off w p, rfl, rfl⟩⟩
  have other : ∀ {i}, stepKD τ i = stepK τ i →
      (stepKD τ i = none ∧ step τ i = none) ∨ ∃ a b, stepKD τ i = some a ∧ step τ i = some b ∧ Sim a b := by
    intro i e
    rw [e, stepK_eq]
    cases step τ i
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨_, _, rfl, rfl, Sim.refl _⟩
  cases i
  case str t n off => exact st n off 4 _
  case strb t n off => exact st n off 1 _
  all_goals exact other rfl

end VG.Arm.Taint

namespace VG.Arm

/-- `taint`, with an order for which it is monotone (`Taint.leS`), and stores
that do not repeat a slot: the same analysis, for checks with summaries
(`taint_summary`, `taint_decide_sum`). -/
def taintS : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.stepKD
  step_sound {τ τ' i s₁ s₂ s₁' s₂'} ha hs e₁ e₂ := by
    rcases Taint.stepKD_spec τ i with ⟨h, -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h] at hs; cases hs
    · rw [h₁] at hs; cases hs
      obtain ⟨h₃, h₄⟩ := Taint.step_sound ha h₂ e₁ e₂
      exact ⟨h₃, hab.agree h₄⟩
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meet
  meet_left := Taint.meet_left
  meet_right := Taint.meet_right
  le := Taint.leS
  le_sound h ha := Taint.leS_sound (Taint.leS_iff.mp h).toLeW ha
  call τ := some (Taint.callStep τ)
  call_sound := Taint.call_sound
  ret τ := some τ
  ret_sound := Taint.ret_sound
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

namespace Taint

theorem callStep_mono {τ σ : T} (h : Le τ σ) : Le (callStep τ) (callStep σ) :=
  ⟨⟨RegSet.erase_mono (RegSet.erase_mono h.regs _) _, (fun e => by cases e), h.lens, (h.bases'.filter _).1,
    h.slots, h.argLen, h.argBases⟩, (h.bases'.filter _).2, h.fnA⟩

end Taint

open VG.Arm.Taint in
instance : VG.Taint.LeFrame taintS where
  le_trans h₁ h₂ := leS_iff.mpr ((leS_iff.mp h₁).trans (leS_iff.mp h₂))
  le_right h := leS_iff.mpr (leS_iff.mp h).right
  step {τ σ τ'} i h hs := by
    have hs : stepKD τ i = some τ' := hs
    rcases stepKD_spec τ i with ⟨h', -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h'] at hs; cases hs
    rw [h₁] at hs; cases hs
    obtain ⟨σ'', h₃, h₄⟩ := step_mono (leS_iff.mp h) i h₂
    rcases stepKD_spec σ i with ⟨-, h'⟩ | ⟨c, d, h₅, h₆, hcd⟩
    · rw [h'] at h₃; cases h₃
    rw [h₆] at h₃; cases h₃
    exact ⟨c, h₅, leS_iff.mpr (h₄.sim hab hcd)⟩
  condPub _ h hc := (leS_iff.mp h).flags hc
  meet h₁ h₂ := leS_iff.mpr ((leS_iff.mp h₁).meetM (leS_iff.mp h₂).toLeW)
  call h hs := by cases hs; exact ⟨_, rfl, leS_iff.mpr (callStep_mono (leS_iff.mp h))⟩
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push _ _ hs := by cases hs
  pop _ _ hs := by cases hs

  join := join
  bot := bot
  join_lub ha hb :=
    let h := join_lub (leS_iff.mp ha) (leS_iff.mp hb)
    ⟨leS_iff.mpr h.1, leS_iff.mpr h.2.1, leS_iff.mpr h.2.2⟩
  frameOf := meet
  frame_le_left b ha := leS_iff.mpr (meet_le_left' (leS_iff.mp ha) b)
  frame_le_right a := fun hb => leS_iff.mpr (meet_le_right' a (leS_iff.mp hb))
  frame_mono F h := leS_iff.mpr ((leS_iff.mp h).meetM (LeW.refl F))
  le_frame hb hc := leS_iff.mpr (le_meet' (leS_iff.mp hb) (leS_iff.mp hc))
  le_meet hb hc := leS_iff.mpr (le_meet' (leS_iff.mp hb) (leS_iff.mp hc))
  bot_le ha := leS_iff.mpr (bot_le' (leS_iff.mp ha))
  bot_valid := leS_iff.mpr bot_valid'
  keeps := keepsI
  keepsCall := keepsCallI
  keeps_bot i := by unfold keepsI; cases dst i <;> simp [regOnly, bot, RegSet.mem, RegSet.empty]
  keepsCall_bot := rfl
  step_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : stepKD σ i = some σ' := hs
    rcases stepKD_spec σ i with ⟨h', -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h'] at hs; cases hs
    rw [h₁] at hs; cases hs
    exact leS_iff.mpr ((step_keeps' i hk (leS_iff.mp hΦF) (leS_iff.mp hΦ) h₂).sim (Sim.refl _) hab)
  call_keeps {F Φ σ σ'} hk hΦF hΦ hs := by
    cases hs
    have hΦ := leS_iff.mp hΦ
    simp only [keepsCallI, Bool.and_eq_true, Bool.not_eq_true'] at hk
    have hc := callStep_mono hΦ.right
    refine leS_iff.mpr (le_of_frame hk.1.1 (leS_iff.mp hΦF) (RegSet.subset_iff.mpr fun j hj => ?_) hc.fn hc.fnA)
    have hF := RegSet.subset_iff.mp (leS_iff.mp hΦF).regs j hj
    have hσ := RegSet.subset_iff.mp hΦ.regs j hj
    have ne : ∀ d : Reg, F.regs.mem d = false → RegIdx.idx d ≠ j := fun d hd e => by
      rw [← e] at hF; rw [RegSet.mem_iff.mpr hF] at hd; cases hd
    exact bit_erase (ne _ hk.2) (bit_erase (ne _ hk.1.2) hσ)
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps _ _ _ _ hs := by cases hs
  pop_keeps _ _ _ _ hs := by cases hs

instance : VG.Taint.CodeEq isa := ⟨@VG.Taint.codeBeq Instr Cond _ _⟩

end VG.Arm
