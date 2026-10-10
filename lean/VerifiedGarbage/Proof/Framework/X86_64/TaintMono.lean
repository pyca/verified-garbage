import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.RegSetOrder

/-!
# Summaries for the x86-64 taint analysis

`taintS` is `X86_64.taint` with an order (`leS`) for which the analysis is
monotone (`Taint.Frame`), so that its checks can use summaries of code they
contain (`taint_summary`, `taint_decide_sum`). It has the same taints, steps
and agreement, so a check with it proves the same `ConstantTime`.

`X86_64.taint`'s order is not monotone: a register may have several known
bases (`bases`), and an access through it uses the first; with more bases
known, another one may come first, and a public slot may be missed. `leS`
compares only taints whose larger side has at most one base per register
(`Fn`), which the analysis keeps (and every taint on entry has). It also
lets a taint that says nothing about memory (no lengths and no slots) be
below any other, so that there is a least taint, `bot`.

A frame of a summary (what the summarized code does not write, `keeps`) is a
set of registers.
-/

namespace VG.X86_64.Taint

open RegSet

private theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

/-! ## The order -/

/-- Each register has at most one known base. -/
def Fn (l : List (Reg × Nat × Nat)) : Prop := ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p = q

/-- `Fn`, for the kernel. -/
def fnK (l : List (Reg × Nat × Nat)) : Bool :=
  KList.all l fun p => KList.all l fun q => !regEq p.1 q.1 || (Nat.beq p.2.1 q.2.1 && Nat.beq p.2.2 q.2.2)

/-- `τ` says nothing more than `σ`, which has at most one base per register. -/
def leS (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && (τ.lens == σ.lens || (τ.lens.isEmpty && τ.slots.isEmpty)) &&
    KList.all τ.bases (memB · σ.bases) && KList.all τ.slots (mem3 · σ.slots) && τ.lo.subset σ.lo &&
    τ.xregs.subset σ.xregs && fnK σ.bases

/-- `leS`, but for `Fn`. -/
structure LeW (τ σ : T) : Prop where
  regs : τ.regs.subset σ.regs = true
  flags : τ.flags = true → σ.flags = true
  lens : τ.lens = σ.lens ∨ (τ.lens = [] ∧ τ.slots = [])
  bases : ∀ p ∈ τ.bases, p ∈ σ.bases
  slots : ∀ p ∈ τ.slots, p ∈ σ.slots
  lo : τ.lo.subset σ.lo = true
  xregs : τ.xregs.subset σ.xregs = true

/-- `leS`, as a proposition. -/
structure Le (τ σ : T) : Prop extends LeW τ σ where
  fn : Fn σ.bases

theorem fnK_iff {l : List (Reg × Nat × Nat)} : fnK l = true ↔ Fn l := by
  simp only [fnK, KList.all_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    regEq_eq, KList.beq_eq, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Fn]
  constructor
  · intro h p hp q hq e
    rcases h p hp q hq with h | ⟨h₁, h₂⟩
    · exact absurd e h
    · exact Prod.ext e (Prod.ext h₁ h₂)
  · intro h p hp q hq
    by_cases e : p.1 = q.1
    · have := h p hp q hq e; subst this; exact .inr ⟨rfl, rfl⟩
    · exact .inl e

theorem leS_iff {τ σ : T} : leS τ σ = true ↔ Le τ σ := by
  simp only [leS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff,
    KList.all_eq, List.all_eq_true, memB_eq, mem3_eq, List.contains_iff_mem, fnK_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hlo⟩, hx⟩, hfn⟩
    exact ⟨⟨hr, fun h => hf.elim (fun e => by rw [e] at h; cases h) id, hl, hb, hs, hlo, hx⟩, hfn⟩
  · rintro ⟨⟨hr, hf, hl, hb, hs, hlo, hx⟩, hfn⟩
    refine ⟨⟨⟨⟨⟨⟨⟨hr, ?_⟩, hl⟩, hb⟩, hs⟩, hlo⟩, hx⟩, hfn⟩
    cases e : τ.flags
    · exact .inl rfl
    · exact .inr (hf e)

/-! ### Soundness of the order -/

theorem le_of_lens {τ σ : T} (h : LeW τ σ) (hl : τ.lens = σ.lens) : le τ σ = true := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem]
  refine ⟨⟨⟨⟨⟨⟨h.regs, ?_⟩, hl⟩, h.bases⟩, h.slots⟩, h.lo⟩, h.xregs⟩
  cases e : τ.flags
  · exact .inl rfl
  · exact .inr (h.flags e)

theorem leS_sound {τ σ : T} {s₁ s₂ : State} (hle : Le τ σ) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ := by
  rcases hle.lens with hl | ⟨hl, hs⟩
  · exact le_sound (le_of_lens hle.toLeW hl) h
  · refine ⟨⟨fun r h' => h.rf.1 r (RegSet.mem_of_subset hle.regs h'), fun hf => h.rf.2 (hle.flags hf)⟩,
      fun hne => absurd hl hne, ⟨fun hne => absurd hl hne, fun p hp => h.wf₁.2 p (hle.bases p hp)⟩,
      ⟨fun hne => absurd hl hne, fun p hp => h.wf₂.2 p (hle.bases p hp)⟩, ?_, ?_,
      fun r hr' => h.lo r (RegSet.mem_of_subset hle.lo hr'), fun r hr' => h.xr r (RegSet.mem_of_subset hle.xregs hr')⟩
    · intro sl hsl; rw [hs] at hsl; cases hsl
    · intro sl hsl; rw [hs] at hsl; cases hsl

/-! ### The order is a preorder -/

theorem Fn.sub {l l' : List (Reg × Nat × Nat)} (h : Fn l') (hs : ∀ p ∈ l, p ∈ l') : Fn l :=
  fun p hp q hq e => h p (hs p hp) q (hs q hq) e

theorem Fn.filter {l : List (Reg × Nat × Nat)} (h : Fn l) (P : Reg × Nat × Nat → Bool) :
    Fn (l.filter P) := h.sub fun _ hp => (List.mem_filter.mp hp).1

theorem LeW.refl (τ : T) : LeW τ τ :=
  ⟨RegSet.subset_refl _, id, .inl rfl, fun _ h => h, fun _ h => h, RegSet.subset_refl _, RegSet.subset_refl _⟩

theorem Le.right {τ σ : T} (h : Le τ σ) : Le σ σ := ⟨LeW.refl σ, h.fn⟩

theorem Le.left {τ σ : T} (h : Le τ σ) : Le τ τ := ⟨LeW.refl τ, h.fn.sub h.bases⟩

theorem LeW.trans {a b c : T} (h₁ : LeW a b) (h₂ : LeW b c) : LeW a c where
  regs := RegSet.subset_trans h₁.regs h₂.regs
  flags h := h₂.flags (h₁.flags h)
  lens := by
    rcases h₁.lens with e₁ | ⟨e₁, s₁⟩
    · rcases h₂.lens with e₂ | ⟨e₂, s₂⟩
      · exact .inl (e₁.trans e₂)
      · refine .inr ⟨e₁.trans e₂, ?_⟩
        cases e : a.slots with
        | nil => rfl
        | cons x _ =>
          have := h₁.slots x (by rw [e]; exact List.mem_cons_self ..)
          rw [s₂] at this; cases this
    · exact .inr ⟨e₁, s₁⟩
  bases p hp := h₂.bases p (h₁.bases p hp)
  slots p hp := h₂.slots p (h₁.slots p hp)
  lo := RegSet.subset_trans h₁.lo h₂.lo
  xregs := RegSet.subset_trans h₁.xregs h₂.xregs

theorem Le.trans {a b c : T} (h₁ : Le a b) (h₂ : Le b c) : Le a c := ⟨h₁.toLeW.trans h₂.toLeW, h₂.fn⟩

/-! ## Monotonicity of the steps -/

section
variable {τ σ : T}

theorem LeW.pubM (h : LeW τ σ) {r : Reg} (hr : pub τ r = true) : pub σ r = true :=
  RegSet.mem_of_subset h.regs hr

theorem LeW.memPubM (h : LeW τ σ) {m : MemOp} (hm : memPub τ m = true) : memPub σ m = true := by
  simp only [memPub, Bool.and_eq_true] at hm ⊢
  refine ⟨h.pubM hm.1, ?_⟩
  have h2 := hm.2
  split at h2 <;> first | rfl | exact h.pubM h2

theorem LeW.srcOkM (h : LeW τ σ) {src : Src} (hs : srcOk τ src = true) : srcOk σ src = true := by
  cases src <;> first | rfl | exact h.memPubM hs

theorem LeW.srcPubM (h : LeW τ σ) {src : Src} (hs : srcPub τ src = true) : srcPub σ src = true := by
  cases src <;> first | rfl | exact h.pubM hs | cases hs

theorem LeW.loPubM (h : LeW τ σ) {src : Src} (hs : loPub τ src = true) : loPub σ src = true := by
  cases src <;> first | cases hs | exact RegSet.mem_of_subset h.lo hs

theorem find_mono {l l' : List (Reg × Nat × Nat)} (hs : ∀ p ∈ l, p ∈ l') (hf : Fn l') {b : Reg}
    {p : Reg × Nat × Nat} (h : l.find? (·.1 == b) = some p) : l'.find? (·.1 == b) = some p := by
  have hp := List.find?_some h
  have hm := hs p (List.mem_of_find?_eq_some h)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome (p := fun x : Reg × Nat × Nat => x.1 == b).mpr ⟨p, hm, hp⟩)
  rw [hq]
  have hq' := List.find?_some hq
  simp only [beq_iff_eq] at hp hq'
  exact congrArg some (hf q (List.mem_of_find?_eq_some hq) p hm (hq'.trans hp.symm))

theorem Le.addrOfM (h : Le τ σ) {m : MemOp} {x : Nat × Nat} (ha : addrOf τ m = some x) :
    addrOf σ m = some x := by
  unfold addrOf at ha ⊢
  split at ha <;> [rename_i hc; cases ha]
  rw [ite_t hc]
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ha
  rw [find_mono h.bases h.fn hp]; rfl

theorem Le.loadPubM (h : Le τ σ) {w : Nat} {src : Src} (hs : loadPub τ w src = true) :
    loadPub σ w src = true := by
  cases src with
  | mem m =>
    simp only [loadPub, slotPub] at hs ⊢
    split at hs <;> rename_i x heq <;> [skip; cases hs]
    rw [h.addrOfM heq]
    obtain ⟨sl, hsl, hp⟩ := List.any_eq_true.mp hs
    exact List.any_eq_true.mpr ⟨sl, h.slots sl hsl, hp⟩
  | _ => cases hs

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
def BLe (a b : List (Reg × Nat × Nat)) : Prop := (∀ p ∈ a, p ∈ b) ∧ Fn b

theorem BLe.filter {a b : List (Reg × Nat × Nat)} (h : BLe a b) (P : Reg × Nat × Nat → Bool) :
    BLe (a.filter P) (b.filter P) :=
  ⟨fun p hp => List.mem_filter.mpr ⟨h.1 p (List.mem_filter.mp hp).1, (List.mem_filter.mp hp).2⟩,
    h.2.filter P⟩

/-- The bases after `d` gets a base computed from those of one register
(selected by `P`), each moved by `g`. -/
theorem BLe.moved {a b : List (Reg × Nat × Nat)} (h : BLe a b) (d r : Reg)
    (P : Reg × Nat × Nat → Bool) (hP : ∀ p, P p = true → p.1 = r) (g : Nat × Nat → Nat × Nat) :
    BLe (a.filter (·.1 != d) ++ (a.filter P).map fun p => (d, g p.2))
      (b.filter (·.1 != d) ++ (b.filter P).map fun p => (d, g p.2)) := by
  refine ⟨fun p hp => ?_, fun p hp q hq e => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_append.mpr (.inl ((h.filter _).1 p hp))
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨x, (h.filter P).1 x hx, rfl⟩))
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
      have hx' := List.mem_filter.mp hx
      have hy' := List.mem_filter.mp hy
      rw [h.2 x hx'.1 y hy'.1 ((hP x hx'.2).trans (hP y hy'.2).symm)]

section
variable {τ σ : T}

theorem Le.bases' (h : Le τ σ) : BLe τ.bases σ.bases := ⟨h.bases, h.fn⟩

theorem Le.killM (h : Le τ σ) (d : Reg) : BLe (kill τ d) (kill σ d) := h.bases'.filter _

theorem Le.movBasesM (h : Le τ σ) (d : Reg) (src : Src) : BLe (movBases τ d src) (movBases σ d src) := by
  cases src with
  | reg r =>
    exact h.bases'.moved d r (·.1 == r) (fun p hp => by simpa only [beq_iff_eq] using hp) id
  | _ => exact h.killM d

theorem Le.aluBasesM (h : Le τ σ) (op : AluOp) (d : Reg) (src : Src) (wide : Bool) :
    BLe (aluBases τ op d src wide) (aluBases σ op d src wide) := by
  unfold aluBases
  split
  · split
    · exact h.bases'.moved d d (·.1 == d) (fun p hp => by simpa only [beq_iff_eq] using hp)
        fun x => (x.1, x.2 + _)
    · exact h.killM d
  · split
    · exact h.bases'.moved d d _ (fun p hp => by
        simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1) fun x => (x.1, x.2 - _)
    · exact h.killM d
  · exact h.killM d

end

/-! ### Slots -/

theorem mem_storeSlots_true {τ : T} {m : MemOp} {w : Nat} {x : Nat × Nat × Nat}
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

theorem mem_storeSlots_false {τ : T} {m : MemOp} {w : Nat} {x : Nat × Nat × Nat}
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

theorem storeSlots_mono {τ σ : T} (h : Le τ σ) (hl : τ.lens = σ.lens) (m : MemOp) (w : Nat)
    {p q : Bool} (hpq : p = true → q = true) :
    ∀ x ∈ storeSlots τ m w p, x ∈ storeSlots σ m w q := by
  intro x hx
  cases p
  · obtain ⟨hs, i, d, ha, hw, ho⟩ := mem_storeSlots_false hx
    exact mem_storeSlots_kept (h.addrOfM ha) (hl ▸ hw) (h.slots x hs) ho q
  · cases hpq rfl
    rcases mem_storeSlots_true hx with hs | ⟨i, d, ha, hw, rfl⟩
    · exact mem_storeSlots_of_mem m w (h.slots x hs)
    · exact mem_storeSlots_new (h.addrOfM ha) (hl ▸ hw)

theorem storeSlots_bot {τ : T} (hl : τ.lens = []) (hs : τ.slots = []) (m : MemOp) {w : Nat} (hw : 0 < w)
    (p : Bool) : storeSlots τ m w p = [] := by
  unfold storeSlots
  split
  · rw [hl, ite_f (by simp only [List.getD_nil]; omega)]
    cases p <;> simp [hs]
  · cases p <;> simp [hs]

/-! ### Steps -/

section
variable {τ σ : T}

theorem Le.upd (h : Le τ σ) {r₁ r₂ : RegSet Reg} (hr : r₁.subset r₂ = true) {f₁ f₂ : Bool}
    (hf : f₁ = true → f₂ = true) {b₁ b₂ : List (Reg × Nat × Nat)} (hb : BLe b₁ b₂)
    {l₁ l₂ : RegSet Reg} (hl : l₁.subset l₂ = true) :
    Le { τ with regs := r₁, flags := f₁, bases := b₁, lo := l₁ }
      { σ with regs := r₂, flags := f₂, bases := b₂, lo := l₂ } :=
  ⟨⟨hr, hf, h.lens, hb.1, h.slots, hl, h.xregs⟩, hb.2⟩

theorem empty_subset' : (RegSet.empty : RegSet Reg).subset RegSet.empty = true := RegSet.subset_refl _

theorem Le.store (h : Le τ σ) (m : MemOp) {w : Nat} (hw : 0 < w) {p q : Bool} (hpq : p = true → q = true)
    {τ' : T} (hs : storeStep τ m w p = some τ') : ∃ σ', storeStep σ m w q = some σ' ∧ Le τ' σ' := by
  unfold storeStep at hs ⊢
  split at hs <;> [rename_i hm; cases hs]
  cases hs
  rw [ite_t (h.toLeW.memPubM hm)]
  refine ⟨_, rfl, ⟨⟨h.regs, h.flags, ?_, h.bases, ?_, h.lo, h.xregs⟩, h.fn⟩⟩
  · rcases h.lens with hl | ⟨hl, hsl⟩
    · exact .inl hl
    · exact .inr ⟨hl, storeSlots_bot hl hsl m hw p⟩
  · rcases h.lens with hl | ⟨hl, hsl⟩
    · exact storeSlots_mono h hl m w hpq
    · intro x hx; rw [storeSlots_bot hl hsl m hw p] at hx; cases hx

theorem Le.memSome (h : Le τ σ) {m : MemOp} {τ' : T}
    (hs : (if memPub τ m = true then some τ else none) = some τ') :
    ∃ σ', (if memPub σ m = true then some σ else none) = some σ' ∧ Le τ' σ' := by
  split at hs <;> [rename_i hm; cases hs]
  cases hs
  exact ⟨σ, by rw [ite_t (h.toLeW.memPubM hm)], h⟩

theorem Le.clearX (h : Le τ σ) : Le (noX τ) (noX σ) := by
  rw [noX_eq, noX_eq]
  exact ⟨⟨h.regs, h.flags, h.lens, h.bases, h.slots, h.lo, RegSet.subset_refl _⟩, h.fn⟩

theorem Le.memSomeX (h : Le τ σ) {m : MemOp} {τ' : T}
    (hs : (if memPub τ m = true then some (noX τ) else none) = some τ') :
    ∃ σ', (if memPub σ m = true then some (noX σ) else none) = some σ' ∧ Le τ' σ' := by
  split at hs <;> [rename_i hm; cases hs]
  cases hs
  exact ⟨noX σ, by rw [ite_t (h.toLeW.memPubM hm)], h.clearX⟩

theorem setX_mono (h : LeW τ σ) (d : XReg) {p q : Bool} (hpq : p = true → q = true) :
    (setX τ d p).subset (setX σ d q) = true := by
  unfold setX
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono h.xregs d
  · exact RegSet.subset_trans (RegSet.erase_subset τ.xregs d)
      (RegSet.subset_trans h.xregs (RegSet.subset_insert σ.xregs d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono h.xregs d

theorem step_mono (h : Le τ σ) (i : Instr) {τ' : T} (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ Le τ' σ' := by
  have hw := h.toLeW
  cases i with
  | mov d src =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t (hw.srcOkM hok)]
    refine ⟨_, rfl, h.upd (set_mono hw d fun hp => ?_) h.flags (h.movBasesM d src) empty_subset'⟩
    simp only [Bool.or_eq_true] at hp ⊢
    exact hp.imp hw.srcPubM h.loadPubM
  | mov32 d src =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t (hw.srcOkM hok)]
    refine ⟨_, rfl, h.upd (set_mono hw d fun hp => ?_) h.flags (h.killM d) empty_subset'⟩
    simp only [Bool.or_eq_true] at hp ⊢
    exact hp.imp (fun hp => hp.imp hw.srcPubM h.loadPubM) hw.loPubM
  | store m r => exact h.store m (by decide) (hw.pubM) hs
  | store32 m r => exact h.store m (by decide) (hw.pubM) hs
  | store8 m r => exact h.store m (by decide) (hw.pubM) hs
  | alu op d src | alu32 op d src =>
    simp only [step, aluStep] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t (hw.srcOkM hok)]
    have hp : (pub τ d && srcPub τ src && (!usesCarry op || τ.flags)) = true →
        (pub σ d && srcPub σ src && (!usesCarry op || σ.flags)) = true := fun hp => by
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp ⊢
      exact ⟨⟨hw.pubM hp.1.1, hw.srcPubM hp.1.2⟩, hp.2.imp id h.flags⟩
    refine ⟨_, rfl, h.upd ?_ hp (h.aluBasesM op d src _) empty_subset'⟩
    cases writes op
    · exact h.regs
    · exact set_mono hw d hp
  | shift32 _ d _ | shift _ d _ =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    refine ⟨_, rfl, h.upd h.regs (fun hp => ?_) (h.killM d) empty_subset'⟩
    simp only [Bool.and_eq_true] at hp ⊢
    exact ⟨h.flags hp.1, hw.pubM hp.2⟩
  | bswap32 d | bswap d =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h.upd h.regs h.flags (h.killM d) empty_subset'⟩
  | rorx32 d r _ | rorx d r _ =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d hw.pubM) h.flags (h.killM d) empty_subset'⟩
  | andn32 d a b | andn d a b =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    have hp : (pub τ a && pub τ b) = true → (pub σ a && pub σ b) = true := fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨hw.pubM hp.1, hw.pubM hp.2⟩
    exact ⟨_, rfl, h.upd (set_mono hw d hp) hp (h.killM d) empty_subset'⟩
  | imul d r =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    have hp : (pub τ d && pub τ r) = true → (pub σ d && pub σ r) = true := fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨hw.pubM hp.1, hw.pubM hp.2⟩
    exact ⟨_, rfl, h.upd (set_mono hw d hp) hp (h.killM d) empty_subset'⟩
  | movImm64 d _ =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d id) h.flags (h.killM d) empty_subset'⟩
  | movzx8 d m =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hm; cases hs]
    cases hs
    rw [ite_t (hw.memPubM hm)]
    exact ⟨_, rfl, h.upd (set_mono hw d id) h.flags (h.killM d) empty_subset'⟩
  | vpmovmskb _ d _ | leaSym d _ =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d id) h.flags (h.killM d) empty_subset'⟩
  | movqR d r =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h.upd (set_mono hw d (RegSet.mem_of_subset hw.xregs)) h.flags (h.killM d) empty_subset'⟩
  | movdquLoad _ m | vmovdquLoad _ _ m | vbroadcasti128 _ m | vbinLoad _ _ _ _ m | vmovdqu32Load _ m
  | vbroadcasti32x4 _ m | vbroadcasti32x4H _ m | zbcst _ _ _ m | vpmadd52Load _ _ _ m | evLoad _ m
  | evMadd52Load _ _ _ m =>
    exact h.memSomeX hs
  | ldmxcsr m => exact h.memSome hs
  | evStore m _ => exact h.store m (by decide) id hs
  | movdquStore m _ => exact h.store m (by decide) id hs
  | vmovdquStore l m _ => cases l <;> exact h.store m (by decide) id hs
  | vmovdqu32Store m _ => exact h.store m (by decide) id hs
  | stmxcsr m => exact h.store m (by decide) id hs
  | xop op =>
    cases op
    case movq d r =>
      simp only [step, Option.some.injEq] at hs ⊢
      cases hs
      exact ⟨_, rfl, ⟨⟨h.regs, h.flags, h.lens, h.bases, h.slots, h.lo, setX_mono hw d hw.pubM⟩, h.fn⟩⟩
    all_goals
      simp only [step, Option.some.injEq] at hs ⊢
      cases hs
      exact ⟨_, rfl, h.clearX⟩
  | vop _ | zop _ | eop _ =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h.clearX⟩
  | lfence =>
    simp only [step, Option.some.injEq] at hs ⊢
    cases hs
    exact ⟨_, rfl, h⟩
  | mul r =>
    simp only [step, Option.some.injEq, mulStep] at hs ⊢
    cases hs
    have hp : (pub τ .rax && pub τ r) = true → (pub σ .rax && pub σ r) = true := fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨hw.pubM hp.1, hw.pubM hp.2⟩
    refine ⟨_, rfl, h.upd ?_ hp ((h.killM .rax).filter _) empty_subset'⟩
    cases e : (pub τ .rax && pub τ r) <;> cases e' : (pub σ .rax && pub σ r) <;>
      simp only [Bool.false_eq_true, ite_true, ite_false]
    · exact RegSet.erase_mono (RegSet.erase_mono h.regs _) _
    · exact RegSet.subset_trans (RegSet.erase_subset _ _) (RegSet.subset_trans
        (RegSet.erase_subset _ _) (RegSet.subset_trans h.regs (RegSet.subset_trans
        (RegSet.subset_insert _ _) (RegSet.subset_insert _ _))))
    · exact absurd (hp e) (by rw [e']; exact Bool.false_ne_true)
    · exact RegSet.insert_mono (RegSet.insert_mono h.regs _) _
  | mulx hi lo src =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t (hw.srcOkM hok)]
    simp only [mulxStep]
    have hp : (pub τ .rdx && srcPub τ src) = true → (pub σ .rdx && srcPub σ src) = true := fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨hw.pubM hp.1, hw.srcPubM hp.2⟩
    refine ⟨_, rfl, h.upd ?_ h.flags ((h.killM hi).filter _) empty_subset'⟩
    cases e : (pub τ .rdx && srcPub τ src) <;> cases e' : (pub σ .rdx && srcPub σ src) <;>
      simp only [Bool.false_eq_true, ite_true, ite_false]
    · exact RegSet.erase_mono (RegSet.erase_mono h.regs _) _
    · exact RegSet.subset_trans (RegSet.erase_subset _ _) (RegSet.subset_trans
        (RegSet.erase_subset _ _) (RegSet.subset_trans h.regs (RegSet.subset_trans
        (RegSet.subset_insert _ _) (RegSet.subset_insert _ _))))
    · exact absurd (hp e) (by rw [e']; exact Bool.false_ne_true)
    · exact RegSet.insert_mono (RegSet.insert_mono h.regs _) _
  | adcx d src | adox d src =>
    simp only [step, adxStep] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t (hw.srcOkM hok)]
    have hp : (pub τ d && srcPub τ src && τ.flags) = true →
        (pub σ d && srcPub σ src && σ.flags) = true := fun hp => by
      simp only [Bool.and_eq_true] at hp ⊢; exact ⟨⟨hw.pubM hp.1.1, hw.srcPubM hp.1.2⟩, h.flags hp.2⟩
    exact ⟨_, rfl, h.upd (set_mono hw d hp) hp (h.killM d) empty_subset'⟩
  | cmov _ d src =>
    simp only [step, cmovStep] at hs ⊢
    split at hs <;> [rename_i hok; cases hs]
    cases hs
    rw [ite_t (hw.srcOkM hok)]
    have hp : (pub τ d && (srcPub τ src || loadPub τ 8 src) && τ.flags) = true →
        (pub σ d && (srcPub σ src || loadPub σ 8 src) && σ.flags) = true := fun hp => by
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hp ⊢
      exact ⟨⟨hw.pubM hp.1.1, hp.1.2.imp hw.srcPubM h.loadPubM⟩, h.flags hp.2⟩
    exact ⟨_, rfl, h.upd (set_mono hw d hp) h.flags (h.killM d) empty_subset'⟩
  | push _ => simp only [step, reduceCtorEq] at hs
  | pop _ _ => simp only [step, reduceCtorEq] at hs
  | alloc _ => simp only [step, reduceCtorEq] at hs
  | free _ => simp only [step, reduceCtorEq] at hs

end

/-! ## Meets and joins -/

section
variable {a b c τ₁ τ₂ σ₁ σ₂ : T}

theorem mem_meet_bases {x : Reg × Nat × Nat} : x ∈ (meet a b).bases ↔ x ∈ a.bases ∧ x ∈ b.bases := by
  simp only [meet, List.mem_filter, List.contains_iff_mem]

theorem mem_meet_slots {x : Nat × Nat × Nat} :
    x ∈ (meet a b).slots ↔ a.lens = b.lens ∧ x ∈ a.slots ∧ x ∈ b.slots := by
  simp only [meet]
  split
  · simp only [List.mem_filter, List.contains_iff_mem, true_and, *]
  · simp only [List.not_mem_nil, false_iff, not_and]; intro h; contradiction

theorem meet_lens : (meet a b).lens = if a.lens = b.lens then a.lens else [] := rfl

/-- A taint that says nothing about memory. -/
theorem lensBot {τ : T} (hl : τ.lens = []) (hs : τ.slots = []) (σ : T) :
    τ.lens = σ.lens ∨ (τ.lens = [] ∧ τ.slots = []) := .inr ⟨hl, hs⟩

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
  lo := RegSet.inter_mono h₁.lo h₂.lo
  xregs := RegSet.inter_mono h₁.xregs h₂.xregs

theorem Le.meetM (h₁ : Le τ₁ σ₁) (h₂ : LeW τ₂ σ₂) : Le (meet τ₁ τ₂) (meet σ₁ σ₂) :=
  ⟨h₁.toLeW.meetM h₂, h₁.fn.sub fun _ hx => (mem_meet_bases.mp hx).1⟩

theorem meet_le_left' (ha : Le a a) (b : T) : Le (meet a b) a := by
  refine ⟨⟨RegSet.inter_subset_left _ _, fun h => ?_, ?_, fun x hx => (mem_meet_bases.mp hx).1,
    fun x hx => (mem_meet_slots.mp hx).2.1, RegSet.inter_subset_left _ _, RegSet.inter_subset_left _ _⟩, ha.fn⟩
  · simp only [meet, Bool.and_eq_true] at h; exact h.1
  · by_cases e : a.lens = b.lens
    · left; rw [meet_lens, ite_t e]
    · exact .inr (meet_bot (.inl e))

theorem meet_le_right' (a : T) (hb : Le b b) : Le (meet a b) b := by
  refine ⟨⟨RegSet.inter_subset_right _ _, fun h => ?_, ?_, fun x hx => (mem_meet_bases.mp hx).2,
    fun x hx => (mem_meet_slots.mp hx).2.2, RegSet.inter_subset_right _ _, RegSet.inter_subset_right _ _⟩,
    hb.fn⟩
  · simp only [meet, Bool.and_eq_true] at h; exact h.2
  · by_cases e : a.lens = b.lens
    · left; rw [meet_lens, ite_t e, e]
    · exact .inr (meet_bot (.inl e))

theorem le_meet' (hb : Le a b) (hc : Le a c) : Le a (meet b c) := by
  refine ⟨⟨RegSet.subset_inter hb.regs hc.regs, fun h => ?_, ?_,
    fun x hx => mem_meet_bases.mpr ⟨hb.bases x hx, hc.bases x hx⟩, fun x hx => ?_,
    RegSet.subset_inter hb.lo hc.lo, RegSet.subset_inter hb.xregs hc.xregs⟩, hb.fn.sub fun _ hx => (mem_meet_bases.mp hx).1⟩
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

/-- The join: what either says is public. Its lengths are those of `a`, unless
`a` says nothing about memory. -/
def join (a b : T) : T where
  regs := a.regs.union b.regs
  flags := a.flags || b.flags
  lens := if a.lens.isEmpty && a.slots.isEmpty then b.lens else a.lens
  bases := a.bases ++ b.bases
  slots := a.slots ++ b.slots
  lo := a.lo.union b.lo
  xregs := a.xregs.union b.xregs

theorem join_lub (ha : Le a c) (hb : Le b c) : Le a (join a b) ∧ Le b (join a b) ∧ Le (join a b) c := by
  have fnJ : Fn (join a b).bases := ha.fn.sub fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ha.bases x hx
    · exact hb.bases x hx
  by_cases hbot : a.lens = [] ∧ a.slots = []
  · have e : (join a b).lens = b.lens := by
      simp only [join, hbot, List.isEmpty_nil, Bool.and_self, ite_true]
    have es : (join a b).slots = b.slots := by simp only [join, hbot, List.nil_append]
    refine ⟨⟨⟨RegSet.subset_union_left _ _, fun h => by simp only [join, h, Bool.true_or], .inr hbot,
        fun x hx => List.mem_append.mpr (.inl hx), fun x hx => List.mem_append.mpr (.inl hx),
        RegSet.subset_union_left _ _, RegSet.subset_union_left _ _⟩, fnJ⟩,
      ⟨⟨RegSet.subset_union_right _ _, fun h => by simp only [join, h, Bool.or_true], .inl e.symm,
        fun x hx => List.mem_append.mpr (.inr hx), fun x hx => List.mem_append.mpr (.inr hx),
        RegSet.subset_union_right _ _, RegSet.subset_union_right _ _⟩, fnJ⟩,
      ⟨⟨RegSet.union_subset ha.regs hb.regs, fun h => ?_, ?_, fun x hx => ?_, fun x hx => ?_,
        RegSet.union_subset ha.lo hb.lo, RegSet.union_subset ha.xregs hb.xregs⟩, hb.fn⟩⟩
    · simp only [join, Bool.or_eq_true] at h; exact h.elim ha.flags hb.flags
    · rw [e, es]; exact hb.lens
    · rcases List.mem_append.mp hx with hx | hx
      · exact ha.bases x hx
      · exact hb.bases x hx
    · rw [es] at hx; exact hb.slots x hx
  · have e : (join a b).lens = a.lens := by
      have : (a.lens.isEmpty && a.slots.isEmpty) = false := by
        cases h1 : a.lens.isEmpty <;> cases h2 : a.slots.isEmpty <;> try rfl
        exact absurd ⟨List.isEmpty_iff.mp h1, List.isEmpty_iff.mp h2⟩ hbot
      simp only [join, this, Bool.false_eq_true, ite_false]
    have eac : a.lens = c.lens := ha.lens.resolve_right hbot
    refine ⟨⟨⟨RegSet.subset_union_left _ _, fun h => by simp only [join, h, Bool.true_or], .inl e.symm,
        fun x hx => List.mem_append.mpr (.inl hx), fun x hx => List.mem_append.mpr (.inl hx),
        RegSet.subset_union_left _ _, RegSet.subset_union_left _ _⟩, fnJ⟩,
      ⟨⟨RegSet.subset_union_right _ _, fun h => by simp only [join, h, Bool.or_true], ?_,
        fun x hx => List.mem_append.mpr (.inr hx), fun x hx => List.mem_append.mpr (.inr hx),
        RegSet.subset_union_right _ _, RegSet.subset_union_right _ _⟩, fnJ⟩,
      ⟨⟨RegSet.union_subset ha.regs hb.regs, fun h => ?_, .inl (e.trans eac), fun x hx => ?_,
        fun x hx => ?_, RegSet.union_subset ha.lo hb.lo, RegSet.union_subset ha.xregs hb.xregs⟩, hb.fn⟩⟩
    · rcases hb.lens with e' | bot
      · exact .inl (by rw [e, eac, e'])
      · exact .inr bot
    · simp only [join, Bool.or_eq_true] at h; exact h.elim ha.flags hb.flags
    · rcases List.mem_append.mp hx with hx | hx
      · exact ha.bases x hx
      · exact hb.bases x hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact ha.slots x hx
      · exact hb.slots x hx

/-- Nothing is public. -/
def bot : T := { regs := .empty, flags := false }

theorem bot_le' (ha : Le a a) : Le bot a :=
  ⟨⟨RegSet.empty_subset _, (fun h => by cases h), .inr ⟨rfl, rfl⟩, (fun _ h => by cases h),
    (fun _ h => by cases h), RegSet.empty_subset _, RegSet.empty_subset _⟩, ha.fn⟩

theorem bot_valid' : Le bot bot := bot_le' ⟨LeW.refl _, fun _ h => by cases h⟩

end

/-! ## Frames: registers that code does not write -/

/-- The registers. -/
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

/-- `F` says only that registers are public. -/
def regOnly (F : T) : Bool :=
  !F.flags && F.lens.isEmpty && F.bases.isEmpty && F.slots.isEmpty && Nat.beq F.lo.bits 0 &&
    Nat.beq F.xregs.bits 0

/-- `i` writes no register of `F`, which says only that registers are public. -/
def keepsI (F : T) (i : Instr) : Bool :=
  regOnly F && KList.all allRegs fun r => !F.regs.mem r || !clobbers i r

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

theorem storeStep_regs {σ σ' : T} {m : MemOp} {w : Nat} {p : Bool} (hs : storeStep σ m w p = some σ') :
    σ'.regs = σ.regs := by
  unfold storeStep at hs
  split at hs <;> [skip; cases hs]
  cases hs; rfl

/-- `i` writes no register of index `j`. -/
def NoWrite (i : Instr) (j : Nat) : Prop := ∀ r, RegIdx.idx r = j → clobbers i r = false

theorem ne_of_dst {i : Instr} {d : Reg} {j : Nat} (hd : dstOf i = some d) (hc : NoWrite i j) :
    RegIdx.idx d ≠ j := by
  intro e
  have := hc d e
  cases i <;> simp_all [clobbers, dstOf]

theorem ne_of_clobbers {i : Instr} {d : Reg} {j : Nat} (hd : clobbers i d = true) (hc : NoWrite i j) :
    RegIdx.idx d ≠ j := by
  intro e; rw [hc d e] at hd; cases hd

/-- A step keeps public the registers the instruction does not write. -/
theorem step_bits {σ σ' : T} {i : Instr} (hs : step σ i = some σ') {j : Nat} (hc : NoWrite i j)
    (hr : σ.regs.bits.testBit j = true) : σ'.regs.bits.testBit j = true := by
  cases i
  case store | store32 | store8 | movdquStore | vmovdqu32Store | stmxcsr | evStore =>
    rw [storeStep_regs hs]; exact hr
  case vmovdquStore l _ _ => cases l <;> (rw [storeStep_regs hs]; exact hr)
  case push | pop | alloc | free => simp only [step, reduceCtorEq] at hs
  case xop op =>
    cases op <;> (simp only [step, Option.some.injEq] at hs; subst hs; first | exact hr | rw [noX_regs]; exact hr)
  case movqR d r =>
    simp only [step, Option.some.injEq] at hs; subst hs; exact bit_set (ne_of_dst rfl hc) hr _
  case mul q =>
    simp only [step, Option.some.injEq, mulStep] at hs
    subst hs
    have h₁ := ne_of_clobbers (d := .rax) (by simp [clobbers]) hc
    have h₂ := ne_of_clobbers (d := .rdx) (by simp [clobbers]) hc
    split
    · exact bit_insert _ (bit_insert _ hr)
    · exact bit_erase h₂ (bit_erase h₁ hr)
  case mulx hi lo src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    simp only [Option.some.injEq, mulxStep] at hs
    subst hs
    have h₁ := ne_of_clobbers (d := hi) (by simp [clobbers]) hc
    have h₂ := ne_of_clobbers (d := lo) (by simp [clobbers]) hc
    split
    · exact bit_insert _ (bit_insert _ hr)
    · exact bit_erase h₁ (bit_erase h₂ hr)
  case alu op d src | alu32 op d src =>
    simp only [step, aluStep] at hs
    split at hs <;> [skip; cases hs]
    simp only [Option.some.injEq] at hs
    subst hs
    show (if writes op = true then _ else σ.regs).bits.testBit j = true
    split
    · exact bit_set (ne_of_dst rfl hc) hr _
    · exact hr
  case adcx d src | adox d src =>
    simp only [step, adxStep] at hs
    split at hs <;> [skip; cases hs]
    simp only [Option.some.injEq] at hs
    subst hs
    exact bit_set (ne_of_dst rfl hc) hr _
  case cmov _ d src =>
    simp only [step, cmovStep] at hs
    split at hs <;> [skip; cases hs]
    simp only [Option.some.injEq] at hs
    subst hs
    exact bit_set (ne_of_dst rfl hc) hr _
  all_goals
    simp only [step] at hs
    first
    | (simp only [Option.some.injEq] at hs; subst hs
       first | exact hr | (rw [noX_regs]; exact hr) | exact bit_set (ne_of_dst rfl hc) hr _)
    | (split at hs <;> [skip; cases hs]
       simp only [Option.some.injEq] at hs; subst hs
       first | exact hr | (rw [noX_regs]; exact hr) | exact bit_set (ne_of_dst rfl hc) hr _)

section
variable {F Φ σ σ' : T}

/-- What a frame keeps public, if `Φ` (below `F`) has the registers. -/
theorem le_of_frame (hk : regOnly F = true) (hΦF : Le Φ F) (hr : Φ.regs.subset σ.regs = true)
    (hfn : Fn σ.bases) : Le Φ σ := by
  simp only [regOnly, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, KList.beq_eq,
    beq_iff_eq] at hk
  obtain ⟨⟨⟨⟨⟨hf, hl⟩, hb⟩, hs⟩, hlo⟩, hx⟩ := hk
  have hs' : Φ.slots = [] := by
    cases e : Φ.slots with
    | nil => rfl
    | cons x _ => have := hΦF.slots x (by rw [e]; exact List.mem_cons_self ..); rw [hs] at this; cases this
  have hlo' : Φ.lo.bits = 0 := by
    have h := hΦF.lo
    rw [RegSet.subset_eq, hlo, Nat.and_zero, beq_iff_eq] at h; exact h.symm
  have hx' : Φ.xregs.bits = 0 := by
    have h := hΦF.xregs
    rw [RegSet.subset_eq, hx, Nat.and_zero, beq_iff_eq] at h; exact h.symm
  refine ⟨⟨hr, (fun h => by have := hΦF.flags h; rw [hf] at this; cases this), ?_, fun x hx => ?_, ?_,
    RegSet.subset_of_bits_zero hlo' _, RegSet.subset_of_bits_zero hx' _⟩, hfn⟩
  · rcases hΦF.lens with e | bot
    · exact .inr ⟨e.trans hl, hs'⟩
    · exact .inr bot
  · have := hΦF.bases x hx; rw [hb] at this; cases this
  · intro x hx; rw [hs'] at hx; cases hx

theorem step_keeps' (i : Instr) (hk : keepsI F i = true) (hΦF : Le Φ F) (hΦ : Le Φ σ)
    (hs : step σ i = some σ') : Le Φ σ' := by
  simp only [keepsI, Bool.and_eq_true, KList.all_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hk
  obtain ⟨σ'', hs', hle⟩ := step_mono hΦ.right i hs
  rw [hs] at hs'; cases hs'
  refine le_of_frame hk.1 hΦF (RegSet.subset_iff.mpr fun j hj => ?_) hle.fn
  refine step_bits hs (fun r e => ?_) (RegSet.subset_iff.mp hΦ.regs j hj)
  have hF : F.regs.mem r = true := RegSet.mem_iff.mpr (e ▸ RegSet.subset_iff.mp hΦF.regs j hj)
  have := hk.2 r (mem_allRegs r)
  rw [hF] at this
  exact this.resolve_left Bool.noConfusion

end

/-! ## Repeated slots -/

theorem Sim.slots_nil {a b : T} (h : Sim a b) (hb : b.slots = []) : a.slots = [] := by
  cases e : a.slots with
  | nil => rfl
  | cons x _ => have := (h.slots x).mp (by rw [e]; exact List.mem_cons_self ..); rw [hb] at this; cases this

theorem Le.sim {a a' b b' : T} (ha : Sim a' a) (hb : Sim b' b) (h : Le a b) : Le a' b' := by
  refine ⟨⟨by rw [ha.regs, hb.regs]; exact h.regs, fun e => by rw [hb.flags]; exact h.flags (ha.flags ▸ e),
    ?_, fun x hx => by rw [hb.bases]; exact h.bases x (ha.bases ▸ hx),
    fun x hx => (hb.slots x).mpr (h.slots x ((ha.slots x).mp hx)), by rw [ha.lo, hb.lo]; exact h.lo,
    by rw [ha.xregs, hb.xregs]; exact h.xregs⟩,
    by rw [hb.bases]; exact h.fn⟩
  rcases h.lens with e | ⟨e, es⟩
  · exact .inl (by rw [ha.lens, hb.lens, e])
  · exact .inr ⟨by rw [ha.lens, e], ha.slots_nil es⟩

/-! ## Calls and returns -/

section
variable {τ σ τ' : T}

theorem callStep_mono (h : Le τ σ) (hs : callStep τ = some τ') : ∃ σ', callStep σ = some σ' ∧ Le τ' σ' := by
  unfold callStep at hs ⊢
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  rw [ite_t (h.toLeW.pubM hp)]
  refine ⟨_, rfl, ⟨⟨h.regs, h.flags, ?_, (h.killM .rsp).1, (fun _ hx => by cases hx), empty_subset', h.xregs⟩,
    (h.killM .rsp).2⟩⟩
  rcases h.lens with e | ⟨e, -⟩
  · exact .inl e
  · exact .inr ⟨e, rfl⟩

theorem retStep_mono (h : Le τ σ) (hs : retStep τ = some τ') : ∃ σ', retStep σ = some σ' ∧ Le τ' σ' := by
  unfold retStep at hs ⊢
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  rw [ite_t (h.toLeW.pubM hp)]
  exact ⟨_, rfl, h.upd h.regs h.flags (h.killM .rsp) empty_subset'⟩

theorem callStep_regs (hs : callStep σ = some τ') : τ'.regs = σ.regs := by
  unfold callStep at hs; split at hs <;> [skip; cases hs]; cases hs; rfl

theorem retStep_regs (hs : retStep σ = some τ') : τ'.regs = σ.regs := by
  unfold retStep at hs; split at hs <;> [skip; cases hs]; cases hs; rfl

end

end VG.X86_64.Taint

namespace VG.X86_64

/-- `taint`, with an order for which it is monotone (`Taint.leS`): the same
analysis, for checks with summaries (`taint_summary`, `taint_decide_sum`). -/
def taintS : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.stepKD
  step_sound := taint.step_sound
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meet
  meet_left := Taint.meet_left
  meet_right := Taint.meet_right
  le := Taint.leS
  le_sound h ha := Taint.leS_sound (Taint.leS_iff.mp h) ha
  call := Taint.callStep
  call_sound := Taint.call_sound
  ret := Taint.retStep
  ret_sound := Taint.ret_sound
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

open VG.X86_64.Taint in
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
  call h hs := by
    obtain ⟨σ', h₁, h₂⟩ := callStep_mono (leS_iff.mp h) hs
    exact ⟨σ', h₁, leS_iff.mpr h₂⟩
  ret h hs := by
    obtain ⟨σ', h₁, h₂⟩ := retStep_mono (leS_iff.mp h) hs
    exact ⟨σ', h₁, leS_iff.mpr h₂⟩
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
  keepsCall := regOnly
  keeps_bot _ := rfl
  keepsCall_bot := rfl
  step_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : stepKD σ i = some σ' := hs
    rcases stepKD_spec σ i with ⟨h', -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h'] at hs; cases hs
    rw [h₁] at hs; cases hs
    exact leS_iff.mpr ((step_keeps' i hk (leS_iff.mp hΦF) (leS_iff.mp hΦ) h₂).sim (Sim.refl _) hab)
  call_keeps {F Φ σ σ'} hk hΦF hΦ hs := by
    have hs : callStep σ = some σ' := hs
    have hΦ := leS_iff.mp hΦ
    obtain ⟨σ'', h₁, h₂⟩ := callStep_mono hΦ.right hs
    rw [hs] at h₁; cases h₁
    exact leS_iff.mpr (le_of_frame hk (leS_iff.mp hΦF) (callStep_regs hs ▸ hΦ.regs) h₂.fn)
  ret_keeps {F Φ σ σ'} hk hΦF hΦ hs := by
    have hs : retStep σ = some σ' := hs
    have hΦ := leS_iff.mp hΦ
    obtain ⟨σ'', h₁, h₂⟩ := retStep_mono hΦ.right hs
    rw [hs] at h₁; cases h₁
    exact leS_iff.mpr (le_of_frame hk (leS_iff.mp hΦF) (retStep_regs hs ▸ hΦ.regs) h₂.fn)
  push_keeps _ _ _ _ hs := by cases hs
  pop_keeps _ _ _ _ hs := by cases hs

instance : VG.Taint.CodeEq isa := ⟨@VG.Taint.codeBeq Instr Cond _ _⟩

end VG.X86_64
