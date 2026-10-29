module

/-!
# Induction on a list from its end

`List.reverseRecOn` without Mathlib (`Mathlib.Data.List.Induction`), for
`induction l using VG.List.reverseRecOn with | nil | append_singleton l a ih`.
-/

@[expose] public section

namespace VG.List

/-- A property of every list, from `[]` and from `l` to `l ++ [a]`. -/
@[elab_as_elim] theorem reverseRecOn {α : Type _} {motive : List α → Prop} (l : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l := by
  rw [← List.reverse_reverse l]
  generalize l.reverse = r
  induction r with
  | nil => exact nil
  | cons a r ih => rw [List.reverse_cons]; exact append_singleton _ _ ih

end VG.List
