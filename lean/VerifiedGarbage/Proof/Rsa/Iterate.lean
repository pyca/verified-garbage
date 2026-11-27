module

public import VerifiedGarbage.Proof.Framework.PowLit

/-! # Iterating a function

`iterN f n x` is Mathlib's `f^[n] x`: many modules state RSA's key recovery with
it, which need not load Mathlib for it. -/

@[expose] public section

namespace VG.Proof.Rsa

/-- `f (… (f x))`, `n` times. -/
def iterN {α : Type _} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterN f n (f x)

theorem iterN_zero {α : Type _} (f : α → α) (x : α) : iterN f 0 x = x := rfl

theorem iterN_succ {α : Type _} (f : α → α) (n : Nat) (x : α) : iterN f (n + 1) x = iterN f n (f x) := rfl

theorem iterN_succ' {α : Type _} (f : α → α) : ∀ (n : Nat) (x : α), iterN f (n + 1) x = f (iterN f n x)
  | 0, _ => rfl
  | n + 1, x => iterN_succ' f n (f x)

end VG.Proof.Rsa
