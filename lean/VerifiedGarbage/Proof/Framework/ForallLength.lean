module

/-!
# Every list of a given length

`forall_length` proves `P` of every list of length `n` from `P [x₁, …, xₙ]`
for every `x₁`, …, `xₙ`: `revert l; refine forall_length (n := 18) ?_; intro
x₁ … x₁₈`, where a `match` on the list (`fun | [x₁, …, x₁₈], …`) refutes every
other length once for each pattern (3 s for 27 elements).
-/

@[expose] public section

namespace VG

/-- `P [x₁, …, xₙ]`, for every `x₁`, …, `xₙ`. -/
def ForallN {α : Type} : (n : Nat) → (List α → Prop) → Prop
  | 0, P => P []
  | n + 1, P => ∀ x, ForallN n fun l => P (x :: l)

theorem forall_length {α : Type} : ∀ {n : Nat} {P : List α → Prop}, ForallN n P → ∀ l, l.length = n → P l
  | 0, _, h, [], _ => h
  | _ + 1, _, h, x :: l, hl => forall_length (h x) l (Nat.succ.inj hl)

end VG
