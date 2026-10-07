import VerifiedGarbage.Proof.Framework.PowLit

namespace VG.Proof.Bignum.Square

/-- The value of the first `n` radix-`r` digits. -/
def value (r : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => value r f n + f n * r ^ n

/-- Products above the diagonal, each counted once. -/
def cross (r : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cross r f n + value r f n * f n * r ^ n

/-- The diagonal products. -/
def diagonal (r : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => diagonal r f n + (f n * r ^ n) * (f n * r ^ n)

theorem decomposition (r : Nat) (f : Nat → Nat) (n : Nat) :
    value r f n * value r f n = diagonal r f n + 2 * cross r f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [value, cross, diagonal]
    grind

end VG.Proof.Bignum.Square
