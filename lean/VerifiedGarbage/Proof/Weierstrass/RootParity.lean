module

public import VerifiedGarbage.Spec.Weierstrass

/-! # Choosing the parity of a recovered root

These facts use only the canonical representatives of an odd modulus,
independently of primality and the square-root algorithm. In particular,
negating zero does not provide an odd root.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

variable {p : Nat} [NeZero p]

/-- A nonzero canonical representative negates to `p - y`. -/
theorem neg_val_of_ne_zero (y : Fin p) (hy : y ≠ 0) :
    (-y).val = p - y.val := by
  have hpos : 0 < y.val := by
    have hn : y.val ≠ 0 := fun h => hy (Fin.ext h)
    omega
  rw [Fin.neg_def]
  exact Nat.mod_eq_of_lt (by have := y.isLt; omega)

/-- The two nonzero roots have opposite parity for an odd modulus. -/
theorem neg_parity_of_ne_zero (hp : p % 2 = 1) (y : Fin p) (hy : y ≠ 0) :
    (-y).val % 2 ≠ y.val % 2 := by
  rw [neg_val_of_ne_zero y hy]
  have := y.isLt
  omega

/-- A nonzero root or its negation has either requested parity. -/
theorem select_root_parity (hp : p % 2 = 1) (y : Fin p) (hy : y ≠ 0)
    {b : Nat} (hb : b < 2) :
    (if y.val % 2 = b then y else -y).val % 2 = b := by
  split
  · assumption
  · have := neg_parity_of_ne_zero hp y hy
    omega

end VG.Proof.Weierstrass
