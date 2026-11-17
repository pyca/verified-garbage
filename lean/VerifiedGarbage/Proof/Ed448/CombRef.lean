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

`vcomb`: `[S]B + [k]A` from the top bit of 456 down, doubling for every bit,
adding the comb's table entry of `S` in the last 114 (the comb's rows, which
share the doublings), and `A` when the bit of `k` is set.

That they agree with the specification (`BaseCombOk`, `VerifyEqCombOk`) needs
the group law: these are `Prop`s, proved in `Proof/Ed448/CombFacts.lean`,
which only registration files import.
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

/-! ## Verification's equation -/

/-- One bit `t`: the point doubled, the comb's entry of row `t` of `S` added if `t` is a row,
and `a` added if the bit `bk` (of `k`) is set. -/
def vcombStep (S : Nat) (bk : Bool) (t : Nat) (a q : Point) : Point :=
  let r₁ := double q
  let r₂ := if t < 114 then Spec.Ed448.pointAdd r₁ (combPoint (combDigit S t)) else r₁
  if bk then Spec.Ed448.pointAdd r₂ a else r₂

/-- The point after the top `m` of the 456 bits of `k`, with the comb's rows of `S` among
them. -/
def vcomb (S K : Nat) (a : Point) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => vcombStep S (bitAt K (455 - m)) (455 - m) a (vcomb S K a m)

theorem vcomb_bit (S K : Nat) (a : Point) {t : Nat} (ht : t < 456) :
    vcomb S K a (456 - t) = vcombStep S (bitAt K t) t a (vcomb S K a (456 - (t + 1))) := by
  rw [show 456 - t = (456 - (t + 1)) + 1 by omega_using [ht], vcomb,
    show 455 - (456 - (t + 1)) = t by omega_using [ht]]

/-- The equation (RFC 8032 §5.2.7) of decoded `A` and `R`: `S < L`, and
`[4]([S]B + [k](-A))` (by `vcomb`) and `[4]R` (by doubling) represent the
same point. -/
def VerifyEqCombOk : Prop :=
  ∀ (pk sig ch : List Byte) (a r : Point), pk.length = 57 → sig.length = 114 → ch.length = 57 →
    Spec.Ed448.decodePoint pk = some a → Spec.Ed448.decodePoint (sig.take 57) = some r →
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual
          (double (double (vcomb (Spec.Ed448.decodeLE (sig.drop 57)) (Spec.Ed448.decodeLE ch)
            (negPoint a) 456)))
          (double (double r)))

end VG.Proof.Ed448
