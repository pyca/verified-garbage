module

/-!
# A function updated at a point

`Mathlib`'s `Function.update`, for functions that are not dependent. The
environments of the field programs (`Proof/Weierstrass/Env.lean`, …) are
built with it, and every module about their code imports it: with no import
of its own, it spares them Mathlib, whose import and linters cost each module
about a fifth of a second.
-/

@[expose] public section

namespace VG.Fun

/-- `f`, with the value `v` at `a`. -/
def update {α β : Type _} [DecidableEq α] (f : α → β) (a : α) (v : β) (x : α) : β :=
  if x = a then v else f x

variable {α β : Type _} [DecidableEq α]

theorem update_apply (f : α → β) (a : α) (v : β) (x : α) :
    update f a v x = if x = a then v else f x := rfl

@[simp] theorem update_self (a : α) (v : β) (f : α → β) : update f a v a = v :=
  ite_eq_left rfl

@[simp] theorem update_of_ne {a a' : α} (h : a ≠ a') (v : β) (f : α → β) :
    update f a' v a = f a := ite_eq_right h

@[simp] theorem update_eq_self (a : α) (f : α → β) : update f a (f a) = f := by
  funext x
  rw [update_apply]
  split
  · next h => rw [h]
  · rfl

@[simp] theorem update_idem {a : α} (v w : β) (f : α → β) :
    update (update f a v) a w = update f a w := by
  funext x
  simp only [update_apply]
  split <;> rfl

end VG.Fun
