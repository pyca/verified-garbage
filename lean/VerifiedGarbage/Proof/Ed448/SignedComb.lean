module

public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Impl.X448.BaseTable
import VerifiedGarbage.Proof.Framework.Omega

/-!
# edwards448: what a signed radix-16 comb of 57 tables computes

Untrusted and target-independent, and light, as `CombRef.lean`: no Mathlib
algebra. The scalar's nibbles `n_i` (`nib`) and the magnitudes of its digits
`n_i - 8` (`mag`). `signedComb`: `[k] B` from the tables of
`Impl/X448/BaseTable.lean`, two accumulators starting at `[G] B` (`baseG57`),
to which step `j < 57` adds table `j`'s entries of the digits `2j + 1` and `2j`
(`signedSum`, by `affAdd`), and `16` times the first plus the second.

That it agrees with the specification (`SignedBaseOk`, and `SignedBaseUOk`: X448
of the base point) needs the group law: these are `Prop`s, proved in
`Proof/Ed448/SignedCombFacts.lean`, which only registration files import.
-/

@[expose] public section

namespace VG.Proof.X448

open Spec.X448 (Fe)

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- A nibble from its four bits. -/
theorem nib_bits (S i : Nat) :
    nib S i = (((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2 := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [Nat.pow_mul]
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [nib, e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [Nat.pow_zero, Nat.div_one, Nat.reducePow]
  omega_arith

theorem nib_lt (S i : Nat) : nib S i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem mag_lt {n : Nat} (hn : n < 16) : mag n < 9 := by unfold mag; split <;> omega_arith

/-- The affine point `(x, y)` negated: `(-x, y)`. -/
def negAff (q : Fe × Fe) : Fe × Fe := (0 - q.1, q.2)

end VG.Proof.X448

namespace VG.Proof.Ed448

open Spec.X448 (Fe)
open Spec.Ed448 (Point)
open VG.Proof.X448 (nib mag negAff)

/-- `(X : Y : Z) + (x, y)`: RFC 8032 §5.2.4's addition, with `Z₂ = 1` and `d = -39081`. -/
def affAdd (p : Point) (q : Fe × Fe) : Point :=
  let b := p.Z * p.Z
  let c := p.X * q.1
  let e := p.Y * q.2
  let t := Spec.X448.a24 * (c * e)
  let k := (p.X + p.Y) * (q.1 + q.2) - c - e
  let f := b + t
  let g := b - t
  ⟨p.Z * f * k, p.Z * g * (e - c), f * g⟩

/-- The entry of table `j` for the nibble `n`, whose digit is `n - 8`. -/
def signedEntry (j n : Nat) : Fe × Fe :=
  if n < 8 then negAff (Impl.X448.baseTable j (mag n)) else Impl.X448.baseTable j (mag n)

/-- `[G + Σ_(j < c) (n_(2j+o) - 8) 256^j] B`. -/
def signedSum (k o : Nat) : Nat → Point
  | 0 => ⟨Impl.X448.baseG57.1, Impl.X448.baseG57.2, 1⟩
  | c + 1 => affAdd (signedSum k o c) (signedEntry c (nib k (2 * c + o)))

/-- `[k] B`. -/
def signedComb (k : Nat) : Point :=
  Spec.Ed448.pointAdd (double (double (double (double (signedSum k 1 57))))) (signedSum k 0 57)

/-- The comb encodes `[k]B`. -/
def SignedBaseOk : Prop :=
  ∀ k, Below456 k → Spec.Ed448.encodePoint (signedComb k) =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul k Spec.Ed448.basePoint)

/-- X448 of the base point (RFC 7748 §6.2) is the u-coordinate `Y² / X²` (with `1 / 0 = 0`) of
the comb's point for the decoded scalar, whose bits from 448 up are zero. -/
def SignedBaseUOk : Prop :=
  ∀ kb : List Byte,
    (∀ t, 448 ≤ t → (Spec.X448.decodeScalar448 kb >>> t) &&& 1 = 0) ∧
    Spec.X448.x448 kb Spec.X448.basePoint = Spec.X448.encodeUCoordinate
      ((signedComb (Spec.X448.decodeScalar448 kb)).Y * (signedComb (Spec.X448.decodeScalar448 kb)).Y *
        Proof.X448.invert ((signedComb (Spec.X448.decodeScalar448 kb)).X *
          (signedComb (Spec.X448.decodeScalar448 kb)).X))

end VG.Proof.Ed448
