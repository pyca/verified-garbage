module


/-!
# Looking up what a test computed before

A known-answer test that checks a vector in several ways often evaluates the
same costly function (a block cipher, a scalar multiplication) on the same
arguments again. `memo table f` is `f` with the arguments of `table` looked
up rather than computed, and is `f` itself when `table` pairs each argument
with `f` of it (`memo_eq`): a test evaluates a check with `memo table f` in
place of `f`, and checks what it would have with `f`.
-/

@[expose] public section

namespace VG.Test

/-- `f`, with the arguments of `table` looked up in it. -/
def memo {α β : Type} [DecidableEq α] : List (α × β) → (α → β) → α → β
  | [], f, x => f x
  | (a, b) :: t, f, x => if x = a then b else memo t f x

theorem memo_eq {α β : Type} [DecidableEq α] (table : List (α × β)) (f : α → β)
    (h : ∀ p ∈ table, p.2 = f p.1) : memo table f = f := by
  funext x
  induction table with
  | nil => rfl
  | cons p t ih =>
    have hp := h p List.mem_cons_self
    have ih := ih fun q hq => h q (List.mem_cons_of_mem p hq)
    by_cases hx : x = p.1
    · simp only [memo, hx, ↓reduceIte, hp]
    · simp only [memo, hx, ↓reduceIte, ih]

/-- `f` on each of the arguments `xs`. -/
def tableOf {α β : Type} (f : α → β) (xs : List α) : List (α × β) := xs.map fun x => (x, f x)

theorem tableOf_ok {α β : Type} (f : α → β) (xs : List α) :
    ∀ p ∈ tableOf f xs, p.2 = f p.1 := fun p hp => by
  simp only [tableOf, List.mem_map] at hp
  obtain ⟨x, _, rfl⟩ := hp
  rfl

theorem memo_tableOf {α β : Type} [DecidableEq α] (f : α → β) (xs : List α) :
    memo (tableOf f xs) f = f :=
  memo_eq _ _ (tableOf_ok f xs)

/-- Two tables, the arguments of the second found with the first. -/
theorem memo_tableOf_append {α β : Type} [DecidableEq α] (f : α → β) (xs ys : List α) :
    memo (tableOf f xs ++ tableOf f ys) f = f := by
  rw [tableOf, tableOf, ← List.map_append]
  exact memo_tableOf f (xs ++ ys)

end VG.Test
