module

public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Impl.Ed448.Comb
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Ed448: what a four-column comb computes

Untrusted and target-independent, and light, as `Ref.lean`: no Mathlib
algebra. `comb`: `[k]B` by the four-column comb of `Impl/Ed448/Comb.lean`,
114 rows from the top, each a doubling (`double`) and the specification's
addition of the affine table entry of the row's four bits of `k`, 114 apart
(`combDigit`), from the neutral point.

That it encodes `[k]B` (`BaseCombOk`) needs the group law: it is a `Prop`,
proved in `Proof/Ed448/CombFacts.lean`, which only registration files import.
-/

@[expose] public section

namespace VG.Proof.Ed448

open Spec.Ed448 (Point)

/-- The table's index for row `t`: bits `t`, `t + 114`, `t + 228` and `t + 342` of `k`. -/
def combDigit (k t : Nat) : Nat :=
  ((k >>> t) &&& 1) + 2 * ((k >>> (t + 114)) &&& 1) + 4 * ((k >>> (t + 228)) &&& 1) +
    8 * ((k >>> (t + 342)) &&& 1)

theorem combDigit_lt (k t : Nat) : combDigit k t < 16 := by
  have h (x : Nat) : x &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h0 := h (k >>> t)
  have h1 := h (k >>> (t + 114))
  have h2 := h (k >>> (t + 228))
  have h3 := h (k >>> (t + 342))
  unfold combDigit
  omega_using [h0, h1, h2, h3]

/-- The table's entry `i`, as a projective point. -/
def combPoint (i : Nat) : Point := ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, 1⟩

/-- A row: the point doubled, and the table's entry of the row's bits added. -/
def combRow (k t : Nat) (r : Point) : Point :=
  Spec.Ed448.pointAdd (double r) (combPoint (combDigit k t))

/-- The point after the top `m` of the 114 rows, from the neutral point: rows 113 down to
`114 - m`. -/
def comb (k : Nat) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => combRow k (113 - m) (comb k m)

/-- The rows from `t` up, after row `t + 1`'s. -/
theorem comb_row (k : Nat) {t : Nat} (ht : t < 114) :
    comb k (114 - t) = combRow k t (comb k (114 - (t + 1))) := by
  rw [show 114 - t = (114 - (t + 1)) + 1 by omega_using [ht], comb,
    show 113 - (114 - (t + 1)) = t by omega_using [ht]]

/-- The comb over all 114 rows encodes `[k]B`. -/
def BaseCombOk : Prop :=
  ∀ k, Below456 k → Spec.Ed448.encodePoint (comb k 114) =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul k Spec.Ed448.basePoint)

end VG.Proof.Ed448
