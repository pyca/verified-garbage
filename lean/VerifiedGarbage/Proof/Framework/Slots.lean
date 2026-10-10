import Lean.ToExpr

/-!
# Public bytes of the writable regions, as bit masks

A taint domain's *public slots* are bytes of the writable regions that hold
the same value in both runs. The kernel evaluates the analysis at every
instruction, and a list of byte ranges makes it compare every range at
every access, and build a new list at every store. A `Slots` keeps, for each
writable region `i`, a `Nat` whose bit `k` says whether byte `k` is public,
so that every access and store is a few native `Nat` operations, whatever
the number of public ranges.

The operations are written with the `Nat` functions themselves (`Nat.lor`,
not `|||`), as `RegSet`'s are; the lists have one entry per writable region,
so their structural recursion costs the kernel little. The module imports
only Lean core, as the precompiled hint search (`NativeHintSearch`) uses it.
The lemmas state the operations in terms of `has`, whether a byte is public.

Code and proofs write slots as lists of ranges `(i, o, n)` (the `n` bytes at
offset `o` of region `i`), which `ofList` (a coercion) turns into masks.
-/

namespace VG

/-- Public bytes: bit `k` of `masks[i]` says whether byte `k` of writable
region `i` is public (`0` past the end of the list). -/
structure Slots where
  masks : List Nat
  deriving DecidableEq

namespace Slots

instance : Lean.ToExpr Slots where
  toExpr s := Lean.mkApp (.const ``Slots.mk []) (Lean.toExpr s.masks)
  toTypeExpr := .const ``Slots []

/-- No public bytes. -/
def empty : Slots := ⟨[]⟩

instance : Inhabited Slots := ⟨empty⟩

/-- Entry `i` of `l`, `0` past its end. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, i + 1 => nth l i

/-- The mask of region `i`. -/
def get (S : Slots) (i : Nat) : Nat := nth S.masks i

/-- `l` with entry `i` replaced by `f` of it, padded with `0`s if `l` is shorter. -/
def modify (f : Nat → Nat) : List Nat → Nat → List Nat
  | [], 0 => [f 0]
  | [], i + 1 => 0 :: modify f [] i
  | a :: l, 0 => f a :: l
  | a :: l, i + 1 => a :: modify f l i

/-- The bits `d` to `d + w - 1`. -/
def bits (d w : Nat) : Nat := Nat.shiftLeft (Nat.sub (Nat.pow 2 w) 1) d

/-- Byte `k` of region `i` is public. -/
def has (S : Slots) (i k : Nat) : Bool := !Nat.beq (Nat.land 1 (Nat.shiftRight (S.get i) k)) 0

/-- The `w` bytes at offset `d` of region `i` are all public. -/
def covers (S : Slots) (i d w : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (S.get i) d) (Nat.sub (Nat.pow 2 w) 1)) (Nat.sub (Nat.pow 2 w) 1)

/-- The `w` bytes at offset `d` of region `i` made public. -/
def add (S : Slots) (i d w : Nat) : Slots := ⟨modify (fun m => Nat.lor m (bits d w)) S.masks i⟩

/-- The `w` bytes at offset `d` of region `i` made secret. -/
def remove (S : Slots) (i d w : Nat) : Slots :=
  ⟨modify (fun m => Nat.xor m (Nat.land m (bits d w))) S.masks i⟩

/-- The bytes public in both. -/
def interL : List Nat → List Nat → List Nat
  | a :: s, b :: t => Nat.land a b :: interL s t
  | _, _ => []

/-- The bytes public in both. -/
def inter (S T : Slots) : Slots := ⟨interL S.masks T.masks⟩

/-- Every byte public in `S` is public in `T`. -/
def subsetL : List Nat → List Nat → Bool
  | [], _ => true
  | a :: s, [] => Nat.beq a 0 && subsetL s []
  | a :: s, b :: t => Nat.beq (Nat.land a b) a && subsetL s t

/-- Every byte public in `S` is public in `T`. -/
def subset (S T : Slots) : Bool := subsetL S.masks T.masks

/-- The ranges `(i, o, n)` of `L`. -/
def ofList (L : List (Nat × Nat × Nat)) : Slots := L.foldr (fun sl S => S.add sl.1 sl.2.1 sl.2.2) empty

instance : Coe (List (Nat × Nat × Nat)) Slots := ⟨ofList⟩

/-- A new region `0` with public bytes `m`, the others renumbered from `1`. -/
def push (m : Nat) (S : Slots) : Slots := ⟨m :: S.masks⟩

/-- Region `0` dropped, the others renumbered from `0`. -/
def pop (S : Slots) : Slots := ⟨S.masks.tail⟩

/-- The masks of every region, transformed by `f` (for weakening a taint:
`f` should clear bits, not set them). -/
def map (f : Nat → Nat) (S : Slots) : Slots := ⟨S.masks.map f⟩

/-- Bytes `d` to `d + w - 1` of every region made secret. -/
def removeAll (S : Slots) (d w : Nat) : Slots := S.map fun m => Nat.xor m (Nat.land m (bits d w))

/-- Only the bytes of `keep` kept public, in every region. -/
def keepAll (S : Slots) (keep : Nat) : Slots := S.map fun m => Nat.land m keep

/-- No byte is public. -/
def isNone (S : Slots) : Bool := S.masks.all fun m => Nat.beq m 0

/-- The bytes public in either. -/
def unionL : List Nat → List Nat → List Nat
  | a :: s, b :: t => Nat.lor a b :: unionL s t
  | [], t => t
  | s, [] => s

/-- The bytes public in either. -/
def union (S T : Slots) : Slots := ⟨unionL S.masks T.masks⟩

/-- Every byte public in `S` is public in `T`, as a proposition. -/
def Sub (S T : Slots) : Prop := ∀ i k, S.has i k = true → T.has i k = true

theorem Sub.refl (S : Slots) : S.Sub S := fun _ _ h => h

theorem Sub.trans {S T U : Slots} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U :=
  fun i k h => h₂ i k (h₁ i k h)

/-! ## Lemmas -/

private theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem nth_eq (l : List Nat) (i : Nat) : nth l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih => cases i with
    | zero => rfl
    | succ j => exact ih j

theorem get_eq (S : Slots) (i : Nat) : S.get i = S.masks.getD i 0 := nth_eq _ _

theorem nth_modify (f : Nat → Nat) (l : List Nat) (i j : Nat) :
    nth (modify f l i) j = if j = i then f (nth l i) else nth l j := by
  induction l generalizing i j with
  | nil =>
    induction i generalizing j with
    | zero => cases j <;> rfl
    | succ i ih => cases j with
      | zero => rfl
      | succ j =>
        show nth (modify f [] i) j = _
        rw [ih]; simp only [nth, Nat.add_right_cancel_iff]
  | cons a l ih => cases i with
    | zero => cases j <;> rfl
    | succ i => cases j with
      | zero => rfl
      | succ j =>
        show nth (modify f l i) j = _
        rw [ih]; simp only [nth, Nat.add_right_cancel_iff]

theorem get_modify (f : Nat → Nat) (S : Slots) (i j : Nat) :
    get ⟨modify f S.masks i⟩ j = if j = i then f (S.get i) else S.get j := nth_modify f S.masks i j

theorem has_eq (S : Slots) (i k : Nat) : S.has i k = (S.get i).testBit k := by
  rw [has, Nat.testBit, bne, beq_eq]; rfl

theorem bits_eq (d w : Nat) : bits d w = (2 ^ w - 1) <<< d := rfl

theorem testBit_bits (d w k : Nat) : (bits d w).testBit k = (decide (d ≤ k) && decide (k < d + w)) := by
  rw [bits_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : d ≤ k
  · simp only [h, decide_true, Bool.true_and]
    exact decide_eq_decide.mpr (by omega)
  · simp only [h, decide_false, Bool.false_and]

@[simp] theorem has_empty (i k : Nat) : empty.has i k = false := by
  rw [has_eq, get_eq]; simp [empty]

theorem has_add (S : Slots) (i d w j k : Nat) :
    (S.add i d w).has j k = (S.has j k || (decide (j = i) && decide (d ≤ k) && decide (k < d + w))) := by
  simp only [add, has_eq, get_modify]
  by_cases hj : j = i
  · subst hj
    simp only [ite_true, decide_true, Bool.true_and]
    show (Nat.lor _ _).testBit k = _
    rw [show Nat.lor (S.get j) (bits d w) = S.get j ||| bits d w from rfl, Nat.testBit_or, testBit_bits]
  · simp only [hj, ite_false, decide_false, Bool.false_and, Bool.or_false]

theorem has_remove (S : Slots) (i d w j k : Nat) :
    (S.remove i d w).has j k = (S.has j k && !(decide (j = i) && decide (d ≤ k) && decide (k < d + w))) := by
  simp only [remove, has_eq, get_modify]
  by_cases hj : j = i
  · subst hj
    simp only [ite_true, decide_true, Bool.true_and]
    show (Nat.xor _ (Nat.land _ _)).testBit k = _
    rw [show Nat.xor (S.get j) (Nat.land (S.get j) (bits d w)) = S.get j ^^^ (S.get j &&& bits d w) from rfl,
      Nat.testBit_xor, Nat.testBit_and, testBit_bits]
    cases (S.get j).testBit k <;> cases decide (d ≤ k) <;> cases decide (k < d + w) <;> rfl
  · simp only [hj, ite_false, decide_false, Bool.false_and, Bool.not_false, Bool.and_true]

theorem covers_iff (S : Slots) (i d w : Nat) :
    S.covers i d w = true ↔ ∀ k, d ≤ k → k < d + w → S.has i k = true := by
  rw [covers, beq_eq, beq_iff_eq,
    show Nat.land (Nat.shiftRight (S.get i) d) (Nat.sub (Nat.pow 2 w) 1) = (S.get i >>> d) &&& (2 ^ w - 1)
      from rfl, show Nat.sub (Nat.pow 2 w) 1 = 2 ^ w - 1 from rfl]
  constructor
  · intro h k hk₁ hk₂
    have := congrArg (·.testBit (k - d)) h
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
    rw [has_eq, show d + (k - d) = k by omega] at *
    rw [show decide (k - d < w) = true from decide_eq_true (by omega), Bool.and_true] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < w
    · rw [← has_eq, h (d + j) (by omega) (by omega)]; simp [hj]
    · simp [hj]

theorem has_inter (S T : Slots) (i k : Nat) : (S.inter T).has i k = (S.has i k && T.has i k) := by
  simp only [has_eq, get_eq, inter]
  obtain ⟨s⟩ := S; obtain ⟨t⟩ := T
  simp only
  induction s generalizing t i with
  | nil => simp [interL]
  | cons a s ih => cases t with
    | nil => simp [interL]
    | cons b t => cases i with
      | zero =>
        show (Nat.land a b).testBit k = _
        rw [show Nat.land a b = a &&& b from rfl, Nat.testBit_and]; rfl
      | succ i => exact ih i t

theorem has_union (S T : Slots) (i k : Nat) : (S.union T).has i k = (S.has i k || T.has i k) := by
  simp only [has_eq, get_eq, union]
  obtain ⟨s⟩ := S; obtain ⟨t⟩ := T
  simp only
  induction s generalizing t i with
  | nil => cases t <;> simp [unionL]
  | cons a s ih => cases t with
    | nil => simp [unionL]
    | cons b t => cases i with
      | zero =>
        show (Nat.lor a b).testBit k = _
        rw [show Nat.lor a b = a ||| b from rfl, Nat.testBit_or]; rfl
      | succ i => exact ih i t

theorem isNone_iff (S : Slots) : S.isNone = true ↔ ∀ i k, S.has i k = false := by
  simp only [isNone, has_eq, get_eq, List.all_eq_true, beq_eq, beq_iff_eq]
  obtain ⟨s⟩ := S
  simp only
  constructor
  · intro h i k
    by_cases hi : i < s.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        h _ (List.getElem_mem hi), Nat.zero_testBit]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none, Nat.zero_testBit]
  · intro h m hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    apply Nat.eq_of_testBit_eq; intro k
    have := h i k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [this, Nat.zero_testBit]

theorem isNone_of_sub {S T : Slots} (h : S.Sub T) (hT : T.isNone = true) : S.isNone = true :=
  (isNone_iff S).mpr fun i k => by
    cases hk : S.has i k
    · rfl
    · have := h i k hk; rw [(isNone_iff T).mp hT i k] at this; cases this

theorem isNone_empty : empty.isNone = true := rfl

theorem subset_iff (S T : Slots) : S.subset T = true ↔ ∀ i k, S.has i k = true → T.has i k = true := by
  simp only [has_eq, get_eq, subset]
  obtain ⟨s⟩ := S; obtain ⟨t⟩ := T
  simp only
  induction s generalizing t with
  | nil => simp [subsetL]
  | cons a s ih =>
    have step : ∀ b : Nat, (Nat.beq (Nat.land a b) a = true ↔ ∀ k, a.testBit k = true → b.testBit k = true) := by
      intro b
      rw [beq_eq, beq_iff_eq, show Nat.land a b = a &&& b from rfl]
      constructor
      · intro h k hk; rw [← h, Nat.testBit_and] at hk; exact (Bool.and_eq_true _ _ ▸ hk).2
      · intro h; apply Nat.eq_of_testBit_eq; intro k
        rw [Nat.testBit_and]; cases hk : a.testBit k
        · rfl
        · rw [h k hk]; rfl
    cases t with
    | nil =>
      show (Nat.beq a 0 && _) = true ↔ _
      rw [Bool.and_eq_true, ih [], beq_eq, beq_iff_eq]
      simp only [List.getD_nil, Nat.zero_testBit]
      constructor
      · rintro ⟨rfl, hr⟩ i k hk
        cases i with
        | zero => simp at hk
        | succ i => exact hr i k hk
      · intro h
        refine ⟨?_, fun i k hk => h (i + 1) k hk⟩
        apply Nat.eq_of_testBit_eq; intro k
        have := h 0 k; simp only [List.getD_cons_zero, Nat.zero_testBit] at this ⊢
        cases hk : a.testBit k
        · rfl
        · exact absurd (this hk) (by simp)
    | cons b t =>
      show (Nat.beq (Nat.land a b) a && _) = true ↔ _
      rw [Bool.and_eq_true, ih t, step b]
      constructor
      · rintro ⟨h0, hr⟩ i k hk
        cases i with
        | zero => exact h0 k hk
        | succ i => exact hr i k hk
      · intro h; exact ⟨h 0, fun i k hk => h (i + 1) k hk⟩

theorem has_ofList (L : List (Nat × Nat × Nat)) (i k : Nat) :
    (ofList L).has i k = true ↔ ∃ sl ∈ L, sl.1 = i ∧ sl.2.1 ≤ k ∧ k < sl.2.1 + sl.2.2 := by
  induction L with
  | nil => simp [ofList]
  | cons sl L ih =>
    show (add (ofList L) sl.1 sl.2.1 sl.2.2).has i k = true ↔ _
    rw [has_add, Bool.or_eq_true, ih]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨⟨h₁, h₂⟩, h₃⟩)
      · exact ⟨x, .inr hx, h⟩
      · exact ⟨sl, .inl rfl, h₁.symm, h₂, h₃⟩
    · rintro ⟨x, rfl | hx, h⟩
      · exact .inr ⟨⟨h.1.symm, h.2.1⟩, h.2.2⟩
      · exact .inl ⟨x, hx, h⟩

theorem has_push_zero (m : Nat) (S : Slots) (k : Nat) : (S.push m).has 0 k = m.testBit k := by
  rw [has_eq]; rfl

theorem has_push_succ (m : Nat) (S : Slots) (i k : Nat) : (S.push m).has (i + 1) k = S.has i k := by
  rw [has_eq, has_eq]; rfl

theorem has_pop (S : Slots) (i k : Nat) : S.pop.has i k = S.has (i + 1) k := by
  simp only [has_eq, get_eq, pop]
  cases S.masks <;> simp

end Slots

end VG
