/-! A bounded `∀` the kernel checks in linear time. `decide +kernel` on
`∀ i : Fin n, p i`, `∀ i < n, p i` or `Nat.all n f` reduces `Nat.brecOn` on a
function of `i < n`, which the kernel takes quadratic time for: over a second
for `n = 1024` even when `p` is trivial. `allBelow f n`, a `Nat.rec`, takes
milliseconds; prove the bounded statement with
`of_allBelow (by decide +kernel)`. -/

namespace VG

/-- `f i` for every `i < n`, by the kernel's `Nat.rec`. Each step calls `and`,
a definition, so the kernel's `whnf` takes the steps in its loop rather than by
nested recursion. -/
def allBelow (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec true (fun i r => f i && r) n

theorem of_allBelow {f : Nat → Bool} {n : Nat} (h : allBelow f n=true) :
    ∀ i<n,f i=true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : (f n && allBelow f n)=true := h
    rw [Bool.and_eq_true] at h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h'.2 i hi
    · exact h'.1

/-- `∀ i : Fin n, p i` from the kernel's evaluation of `allBelow`. -/
theorem forall_fin_of_allBelow {n : Nat} (p : Nat → Prop) [DecidablePred p]
    (h : allBelow (fun i => decide (p i)) n=true) : ∀ i : Fin n,p i.val :=
  fun i => of_decide_eq_true (of_allBelow h i.val i.isLt)

end VG
