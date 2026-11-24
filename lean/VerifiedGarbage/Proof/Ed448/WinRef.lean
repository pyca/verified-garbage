module

public import VerifiedGarbage.Proof.Ed448.CombRef
public import VerifiedGarbage.Proof.Ed448.SignedComb
public import VerifiedGarbage.Impl.Ed448.PublicTable
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Ed448: what verification's two sliding windows compute

Untrusted and target-independent, and light, as `CombRef.lean`. `vwin`:
`[S]B + [k]A` from the top bit of 456 down, doubling for every bit; where the
digit of `S` there, in windows of seven bits (`bdigits`), is not zero, the odd
multiple of `B` by it (`Impl/Ed448/PublicTable.lean`, affine) is added, and
where `k`'s, in windows of four (`vdigits`), is not, the odd multiple of `A`
(`oddMul`).

That this agrees with the specification (`VerifyEqWinOk`) is proved in
`Proof/Ed448/WinFacts.lean`, which only registration files import.
-/

@[expose] public section

namespace VG.Proof.Ed448

open Spec.Ed448 (Point)

/-- The digits of the 456-bit `S`: each zero or odd and below 128. -/
abbrev bdigits (S : Nat) : Nat → Nat := Proof.Ed25519.Slide.digitsW 7 456 S

/-- One bit: the point doubled, the multiple of `B` by the digit `ds` (of `S`) added if it is not
zero, and the multiple of `a` by the digit `dk` (of `k`), if it is not zero. -/
def vwinStep (ds dk : Nat) (a q : Point) : Point :=
  let r₁ := double q
  let r₂ := if ds = 0 then r₁ else affAdd r₁ (Impl.Ed448.PublicTable.entry ((ds - 1) / 2))
  if dk = 0 then r₂ else Spec.Ed448.pointAdd r₂ (oddMul a ((dk - 1) / 2))

/-- The point after the top `m` of the 456 digits of `S` and `k`. -/
def vwin (S K : Nat) (a : Point) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => vwinStep (bdigits S (455 - m)) (vdigits K (455 - m)) a (vwin S K a m)

theorem vwin_bit (S K : Nat) (a : Point) {t : Nat} (ht : t < 456) :
    vwin S K a (456 - t) = vwinStep (bdigits S t) (vdigits K t) a (vwin S K a (456 - (t + 1))) := by
  rw [show 456 - t = (456 - (t + 1)) + 1 by omega_using [ht], vwin,
    show 455 - (456 - (t + 1)) = t by omega_using [ht]]

/-- The equation (RFC 8032 §5.2.7) of decoded `A` and `R`: `S < L`, and
`[4]([S]B + [k](-A))` (by `vwin`) and `[4]R` (by doubling) represent the
same point. -/
def VerifyEqWinOk : Prop :=
  ∀ (pk sig ch : List Byte) (a r : Point), pk.length = 57 → sig.length = 114 → ch.length = 57 →
    Spec.Ed448.decodePoint pk = some a → Spec.Ed448.decodePoint (sig.take 57) = some r →
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual
          (double (double (vwin (Spec.Ed448.decodeLE (sig.drop 57)) (Spec.Ed448.decodeLE ch)
            (negPoint a) 456)))
          (double (double r)))

end VG.Proof.Ed448
