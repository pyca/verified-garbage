import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Reordering schedules of commuting operations

A checker, evaluated by the kernel, that a schedule of operations computes the
same as another order of them. Each operation has a key (its place in the
target order) and a mask (a bit for each part of the state it touches), and
operations with disjoint masks commute. The schedule is given as slices: each
slice is sorted by checked insertion, which moves an operation only past
operations disjoint from it, and the sorted slices, whose masks must be
disjoint as wholes, are merged without checks. The insertion is quadratic in
the length of a slice, the rest linear in the whole schedule, where sorting
all of it by insertion would be quadratic in its length.
-/

namespace VG.Proof.MlDsa.Schedule

variable {α β : Type}

/-- Runs `ops` in order. -/
def run (f : α → β → β) (ops : List α) (w : β) : β := ops.foldl (fun w o => f o w) w

/-- The union of the masks of `ops`. -/
def maskAll (mask : α → Nat) : List α → Nat
  | [] => 0
  | a :: as => mask a ||| maskAll mask as

/-- Checked insertion: `a` moves only past operations disjoint from it. -/
def insert (key mask : α → Nat) (a : α) : List α → Option (List α)
  | [] => some [a]
  | b :: bs => bif Nat.ble (key a) (key b) then some (a :: b :: bs)
      else bif Nat.beq (mask a &&& mask b) 0 then (insert key mask a bs).map (b :: ·)
      else none

/-- Sorts `ops` by checked insertion. -/
def normalize (key mask : α → Nat) : List α → Option (List α)
  | [] => some []
  | a :: as => (normalize key mask as).bind (insert key mask a)

/-- Merges `x :: xs` into `ys`, with `rec` merging `xs`. -/
def mergeGo (key : α → Nat) (x : α) (xs : List α) (rec : List α → List α) :
    List α → List α
  | [] => x :: xs
  | y :: ys => bif Nat.ble (key x) (key y) then x :: rec (y :: ys)
      else y :: mergeGo key x xs rec ys

/-- Merges two sorted lists, unchecked. -/
def merge (key : α → Nat) : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => mergeGo key x xs (merge key xs) ys

/-- Sorts each slice by checked insertion and merges the sorted slices, each
disjoint from the merge of those after it. -/
def check (key mask : α → Nat) : List (List α) → Option (List α)
  | [] => some []
  | s :: ss => match check key mask ss, normalize key mask s with
    | some r, some t =>
      bif Nat.beq (maskAll mask t &&& maskAll mask r) 0 then some (merge key t r)
      else none
    | _, _ => none

section
variable {f : α → β → β}

theorem run_cons (a : α) (as : List α) (w : β) : run f (a :: as) w = run f as (f a w) := rfl

theorem run_append (as bs : List α) (w : β) : run f (as ++ bs) w = run f bs (run f as w) :=
  List.foldl_append ..

/-- An operation commuting with each of `l` commutes with running `l`. -/
theorem run_comm {y : α} {l : List α} (h : ∀ z ∈ l, ∀ w, f y (f z w) = f z (f y w))
    (w : β) : run f l (f y w) = f y (run f l w) := by
  induction l generalizing w with
  | nil => rfl
  | cons z zs ih =>
    rw [run_cons, run_cons, ← h z (List.mem_cons_self ..),
      ih (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))]

variable {key mask : α → Nat}
  (hc : ∀ a b, (mask a &&& mask b) = 0 → ∀ w, f b (f a w) = f a (f b w))
include hc

theorem insert_run {a : α} {xs ys : List α} (h : insert key mask a xs = some ys) (w : β) :
    run f ys w = run f xs (f a w) := by
  induction xs generalizing ys w with
  | nil => cases h; rfl
  | cons b bs ih =>
    simp only [insert] at h
    cases hk : Nat.ble (key a) (key b) <;> simp only [hk, Bool.cond_true, Bool.cond_false] at h
    · cases hd : Nat.beq (mask a &&& mask b) 0 <;>
        simp only [hd, Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
      cases he : insert key mask a bs with
      | none => simp only [he, Option.map_none, reduceCtorEq] at h
      | some zs =>
        simp only [he, Option.map_some, Option.some.injEq] at h
        subst ys
        rw [run_cons, run_cons, ih he, hc a b (Nat.eq_of_beq_eq_true hd)]
    · cases h; rfl

theorem normalize_run {xs ys : List α} (h : normalize key mask xs = some ys) (w : β) :
    run f ys w = run f xs w := by
  induction xs generalizing ys w with
  | nil => cases h; rfl
  | cons a xs ih =>
    simp only [normalize] at h
    cases he : normalize key mask xs with
    | none => simp only [he, Option.bind_none, reduceCtorEq] at h
    | some zs =>
      simp only [he, Option.bind_some] at h
      rw [insert_run hc h, ih he, run_cons]

omit hc in
theorem testBit_maskAll {a : α} {l : List α} (ha : a ∈ l) {i : Nat}
    (hi : (mask a).testBit i = true) : (maskAll mask l).testBit i = true := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    simp only [maskAll, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hb
    · exact Or.inl hi
    · exact Or.inr (ih hb)

omit hc in
theorem land_of_maskAll {t r : List α} (h : (maskAll mask t &&& maskAll mask r) = 0)
    {a b : α} (ha : a ∈ t) (hb : b ∈ r) : (mask a &&& mask b) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (·.testBit i) h
  simp only [Nat.zero_testBit, Nat.testBit_and] at hi ⊢
  rcases Bool.eq_false_or_eq_true ((mask a).testBit i) with ha' | ha'
  · rcases Bool.eq_false_or_eq_true ((mask b).testBit i) with hb' | hb'
    · rw [testBit_maskAll ha ha', testBit_maskAll hb hb'] at hi
      simp at hi
    · simp only [hb', Bool.and_false]
  · simp only [ha', Bool.false_and]

theorem merge_run {t r : List α}
    (h : ∀ a ∈ t, ∀ b ∈ r, (mask a &&& mask b) = 0) (w : β) :
    run f (merge key t r) w = run f (t ++ r) w := by
  induction t generalizing r w with
  | nil => rfl
  | cons x xs ih =>
    simp only [merge]
    induction r generalizing w with
    | nil => simp only [mergeGo, List.append_nil]
    | cons y ys ihr =>
      simp only [mergeGo]
      cases hk : Nat.ble (key x) (key y) <;> simp only [Bool.cond_true, Bool.cond_false]
      · rw [run_cons, ihr (fun a ha b hb => h a ha b (List.mem_cons_of_mem _ hb)),
          run_append, run_append,
          run_comm (l := x :: xs) (fun z hz w => hc z y (h z hz y (List.mem_cons_self ..)) w),
          run_cons y ys]
      · rw [run_cons, ih (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b hb)]
        rfl

theorem check_run {ss : List (List α)} {ys : List α} (h : check key mask ss = some ys)
    (w : β) : run f ys w = run f ss.flatten w := by
  induction ss generalizing ys w with
  | nil => cases h; rfl
  | cons s ss ih =>
    simp only [check] at h
    split at h
    · rename_i r t hr ht
      cases hd : Nat.beq (maskAll mask t &&& maskAll mask r) 0 <;>
        simp only [hd, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
      subst ys
      rw [merge_run hc (fun a ha b hb => land_of_maskAll (Nat.eq_of_beq_eq_true hd) ha hb),
        run_append, List.flatten_cons, run_append, normalize_run hc ht, ih hr]
    · cases h

end

/-- The coefficients a butterfly on `j` and `j + len` touches, as bits, or all
of them if it is not a butterfly of a 256-coefficient polynomial. -/
def bflyMask (j len : Nat) : Nat :=
  bif Nat.blt 0 len && Nat.blt (j+len) 256 then 2^j ||| 2^(j+len) else 2^256-1

theorem testBit_bflyMask {j len i : Nat} :
    (bflyMask j len).testBit i = if 0 < len ∧ j+len < 256 then
      decide (j = i ∨ j+len = i) else decide (i < 256) := by
  have hc : (Nat.blt 0 len && Nat.blt (j+len) 256) = decide (0 < len ∧ j+len < 256) :=
    Bool.eq_iff_iff.2 (by simp only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq])
  unfold bflyMask
  rw [hc]
  by_cases h : 0 < len ∧ j+len < 256
  · simp only [h, and_self, decide_true, ite_true, Bool.cond_true, Nat.testBit_or,
      Nat.testBit_two_pow, Bool.decide_or]
  · simp only [h, decide_false, ite_false, Bool.cond_false, Nat.testBit_two_pow_sub_one]

/-- Butterflies with disjoint masks are valid and touch different coefficients. -/
theorem bflyMask_disjoint {j len k step : Nat} (h : (bflyMask j len &&& bflyMask k step) = 0) :
    0 < len ∧ j+len < 256 ∧ 0 < step ∧ k+step < 256 ∧
      j ≠ k ∧ j ≠ k+step ∧ j+len ≠ k ∧ j+len ≠ k+step := by
  have hi : ∀ i, (bflyMask j len).testBit i = true → (bflyMask k step).testBit i = true →
      False := by
    intro i ha hb
    have := congrArg (·.testBit i) h
    simp only [Nat.testBit_and, ha, hb, Bool.and_self, Nat.zero_testBit, Bool.true_eq_false] at this
  simp only [testBit_bflyMask] at hi
  by_cases ha : 0 < len ∧ j+len < 256 <;> by_cases hb : 0 < step ∧ k+step < 256 <;>
    simp only [ha, hb, and_self, ite_true, ite_false, decide_eq_true_eq] at hi
  · refine ⟨ha.1, ha.2, hb.1, hb.2, ?_, ?_, ?_, ?_⟩ <;> intro he
    · exact hi j (Or.inl rfl) (Or.inl he.symm)
    · exact hi j (Or.inl rfl) (Or.inr he.symm)
    · exact hi (j+len) (Or.inr rfl) (Or.inl he.symm)
    · exact hi (j+len) (Or.inr rfl) (Or.inr he.symm)
  · exact (hi j (Or.inl rfl) (by omega)).elim
  · exact (hi k (by omega) (Or.inl rfl)).elim
  · exact (hi 0 (by omega) (by omega)).elim

end VG.Proof.MlDsa.Schedule
