import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Inversion by divsteps: the result in Montgomery form, as a statement

`InvToM p` is what `InvArith.lean`'s `inv_toM` proves for a prime `p > 2`
(`invToM_of_prime`), stated without Mathlib's algebra (`ZMod`), so that a
proof of an inversion takes it as a hypothesis and only the modules that
supply it import that algebra.
-/

namespace VG.Proof.Weierstrass

/-- With `f = ±1`, `x (f a) K ≡ 1` (or `a = 0` for `x = 0`) and
`C_f ≡ f K R³`, the Montgomery product of `a` and `C_f` reads (in Montgomery
form) as `x ^ (p - 2)`. -/
def InvToM (p : Nat) [NeZero p] : Prop :=
  ∀ {R X a Cs acc K : Nat} {f : Int}, 2 < p → UnitMod p R → X < p → (X = 0 → a = 0) →
    (X ≠ 0 → ((X : Int) * (f * a) * K) % p = 1 % p) →
    (X ≠ 0 → (Cs : Int) % p = (f * (K * R ^ 3)) % p) → acc * R % p = a * Cs % p →
    toM p R acc = toM p R X ^ (p - 2)

end VG.Proof.Weierstrass
