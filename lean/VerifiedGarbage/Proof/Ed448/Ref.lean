import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448: what code computes, and its agreement with the specification

Untrusted and target-independent, and light: no Mathlib algebra, so that
every target's proofs can import it. The reference computations here are
what Ed448 code computes, on the specification's field elements and
projective points:

* `double`, RFC 8032 §5.2.4's doubling formulas, and `negPoint`, `-x` as
  `0 - x`;
* `ladder`: `[k]B` from the top bit of 456 down, doubling and adding `B`
  when the bit is set, from the neutral point;
* `vladder`: `[S]B + [k]A` the same way, adding `B` for the bits of `S` and
  `A` for those of `k`;
* `recoverRef`: `recoverX` with its products associated as code computes
  them, and the power by `rootPow`'s addition chain.

That they agree with the specification (`BaseLadderOk`, `VerifyEqOk`,
`RecoverOk`) needs the group law over `ZMod p`, which is heavy: these are
`Prop`s, proved once in `Proof/Ed448/Facts.lean`. A target's proofs take
them as hypotheses, and only its registration files import `Facts` and
pass them in.
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)

/-! ## Doubling and negation -/

/-- `B = (X+Y)²`, `C = X²`, `D = Y²`, `E = C+D`, `H = Z²`, `J = E-2H`, and
`((B-E)J, E(C-D), EJ)` (RFC 8032 §5.2.4). -/
def double (p : Point) : Point :=
  let b := (p.X + p.Y) * (p.X + p.Y)
  let c := p.X * p.X
  let dd := p.Y * p.Y
  let e := c + dd
  let h := p.Z * p.Z
  let j := e - (h + h)
  ⟨(b - e) * j, e * (c - dd), e * j⟩

section
variable (p : Point)

theorem double_X : (double p).X = ((p.X + p.Y) * (p.X + p.Y) - (p.X * p.X + p.Y * p.Y)) *
    (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) := rfl

theorem double_Y : (double p).Y = (p.X * p.X + p.Y * p.Y) * (p.X * p.X - p.Y * p.Y) := rfl

theorem double_Z : (double p).Z = (p.X * p.X + p.Y * p.Y) *
    (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) := rfl

end

/-- `⟨-X, Y, Z⟩`. -/
def negPoint (p : Point) : Point := ⟨0 - p.X, p.Y, p.Z⟩

/-! ## Base-point multiplication -/

/-- `k` has at most 456 bits, as the 57 bytes of a scalar do. (Stated here,
without Mathlib, so that `2 ^ 456` has the instances of the specification's
terms.) -/
def Below456 (k : Nat) : Prop := k < 2 ^ 456

theorem shift_456 {k : Nat} (hk : Below456 k) : k >>> 456 = 0 :=
  (Nat.shiftRight_eq_div_pow k 456).trans (Nat.div_eq_of_lt hk)

theorem decodeLE_below {bs : List Byte} (h : bs.length = 57) : Below456 (Spec.Ed448.decodeLE bs) := by
  have := decodeLE_lt' bs
  rw [h] at this
  exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))

/-- Bit `t` of `k`. -/
def bitAt (k t : Nat) : Bool := decide ((k >>> t) &&& 1 = 1)

/-- One bit: the point doubled, and `B` added if the bit is set. -/
def ladderStep (b : Bool) (r : Point) : Point :=
  if b then Spec.Ed448.pointAdd (double r) Spec.Ed448.basePoint else double r

/-- The point after the top `m` of the 456 bits of `k`, from the neutral
point: bits 455 down to `456 - m`. -/
def ladder (k : Nat) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => ladderStep (bitAt k (455 - m)) (ladder k m)

/-- The bits from `t` up, after bit `t + 1`'s. -/
theorem ladder_bit (k : Nat) {t : Nat} (ht : t < 456) :
    ladder k (456 - t) = ladderStep (bitAt k t) (ladder k (456 - (t + 1))) := by
  rw [show 456 - t = (456 - (t + 1)) + 1 by omega, ladder, show 455 - (456 - (t + 1)) = t by omega]

/-- The ladder over all 456 bits encodes `[k]B`. -/
def BaseLadderOk : Prop :=
  ∀ k, Below456 k → Spec.Ed448.encodePoint (ladder k 456) =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul k Spec.Ed448.basePoint)

/-- A point's encoding, as code computes it: the 56 bytes of `y = Y/Z` and
the low bit of `x = X/Z` as the top bit of the 57th, with `1/Z` by X448's
addition chain. -/
theorem encodePoint_code (X Y Z : Fe) :
    Spec.Ed448.encodePoint ⟨X, Y, Z⟩ =
      Proof.X25519.leBytes 56 (Y * Proof.X448.invert Z).val ++
        [BitVec.ofNat 8 (128 * ((X * Proof.X448.invert Z).val % 2))] := by
  unfold Spec.Ed448.encodePoint
  dsimp only [-Nat.reducePow]
  rw [Proof.X448.invert_eq, encodeLE_57 _ _ (Nat.lt_trans (Fin.isLt _) (by decide +kernel))]

/-! ## Verification's equation -/

/-- One bit of both scalars: the point doubled, `B` added if the bit of `S`
is set, and `a` if that of `k` is. -/
def vstepRef (bs bk : Bool) (a q : Point) : Point :=
  let r₁ := double q
  let r₂ := if bs then Spec.Ed448.pointAdd r₁ Spec.Ed448.basePoint else r₁
  if bk then Spec.Ed448.pointAdd r₂ a else r₂

/-- The point after the top `m` of the 456 bits of `S` and `k`. -/
def vladder (S K : Nat) (a : Point) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => vstepRef (bitAt S (455 - m)) (bitAt K (455 - m)) a (vladder S K a m)

theorem vladder_bit (S K : Nat) (a : Point) {t : Nat} (ht : t < 456) :
    vladder S K a (456 - t) = vstepRef (bitAt S t) (bitAt K t) a (vladder S K a (456 - (t + 1))) := by
  rw [show 456 - t = (456 - (t + 1)) + 1 by omega, vladder, show 455 - (456 - (t + 1)) = t by omega]

/-- The equation (RFC 8032 §5.2.7) of decoded `A` and `R`: `S < L`, and
`[4]([S]B + [k](-A))` (by `vladder`) and `[4]R` (by doubling) represent the
same point. -/
def VerifyEqOk : Prop :=
  ∀ (pk sig ch : List Byte) (a r : Point), pk.length = 57 → sig.length = 114 → ch.length = 57 →
    Spec.Ed448.decodePoint pk = some a → Spec.Ed448.decodePoint (sig.take 57) = some r →
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual
          (double (double (vladder (Spec.Ed448.decodeLE (sig.drop 57)) (Spec.Ed448.decodeLE ch)
            (negPoint a) 456)))
          (double (double r)))

theorem verifyEquation_none {pk sig ch : List Byte}
    (h : Spec.Ed448.decodePoint pk = none ∨ Spec.Ed448.decodePoint (sig.take 57) = none) :
    Spec.Ed448.verifyEquation pk sig ch = false := by
  unfold Spec.Ed448.verifyEquation
  split
  · rfl
  · rcases h with h | h
    · simp only [h]
    · rw [h]; cases Spec.Ed448.decodePoint pk <;> rfl

/-! ## Decoding -/

/-- `recoverX` (RFC 8032 §5.2.3) as code computes it: `v = d y² - 1`,
`u⁵v³ = (u³v)(uv)²`, the power by `rootPow`'s addition chain, the check
`v x² = u`, and `-x = (x - x) - x`. -/
def recoverRef (y : Fe) (sign : Bool) : Option Fe :=
  let u := y * y - 1
  let v := Spec.Ed448.d * (y * y) - 1
  let t := u * u * u * v
  let x := t * rootPow (t * ((u * v) * (u * v)))
  if v * (x * x) ≠ u then none
  else if x = 0 && sign then none
  else some (if (x.val % 2 == 1) == sign then x else (x - x) - x)

/-- `recoverX` is `recoverRef`. -/
def RecoverOk : Prop := ∀ y sign, Spec.Ed448.recoverX y sign = recoverRef y sign

end VG.Proof.Ed448
