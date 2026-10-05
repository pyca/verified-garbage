import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Nat.Prime.Defs

/-!
# Inversion by divsteps: the statement of its result in Montgomery form

The inversion ends with `f = ±1`, `x (f a) K ≡ 1` (`K = 2^(5 B)`, or `a = 0`
for `x = 0`) and multiplies `a` by `C_f ≡ f K R³` in Montgomery form, which
leaves `toM acc = toM x ^ (p - 2)` for a prime `p > 2`: `InvToM`, without
its proof (`InvArith.lean`), which is in `ZMod p` with Mathlib's algebra.
The proofs of the inversions take it as a hypothesis, as they take the
group law, from the curve's variant (`HasLaw.lean`), so that the
modules proving them do not load that algebra.
-/

namespace VG.Proof.Weierstrass

/-- The inversion's last step gives `x ^ (p - 2)`, for any prime `p > 2`. -/
def InvToM : Prop :=
  ∀ {p R X a Cs acc K : Nat} [NeZero p] {f : Int}, p.Prime → 2 < p → UnitMod p R → X < p →
    (X = 0 → a = 0) → (X ≠ 0 → ((X : Int) * (f * a) * K) % p = 1 % p) →
    (X ≠ 0 → (Cs : Int) % p = (f * (K * R ^ 3)) % p) → acc * R % p = a * Cs % p →
    toM p R acc = toM p R X ^ (p - 2)

end VG.Proof.Weierstrass
