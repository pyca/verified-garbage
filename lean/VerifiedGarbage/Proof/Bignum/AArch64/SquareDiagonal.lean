module
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-! Arithmetic identities for doubling cross products and adding a diagonal. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Proof.Bignum

theorem boolWord (c : Bool) :
    (BitVec.ofBool c).setWidth 64 = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

/-- A two-word addition, retaining its third word as an explicit carry bit. -/
theorem pair_add_val (a b x y : BitVec 64) :
    let c := decide (2 ^ 64 ≤ a.toNat + x.toNat)
    let lo := a + x
    let hi := b + y + BitVec.ofNat 64 c.toNat
    lo.toNat + 2 ^ 64 * hi.toNat + 2 ^ 128 *
        (decide (2 ^ 64 ≤ b.toNat + y.toNat + c.toNat)).toNat =
      a.toNat + 2 ^ 64 * b.toNat + x.toNat + 2 ^ 64 * y.toNat := by
  dsimp only
  have hl := adc_toNat a x false
  have hh := adc_toNat b y (decide (2 ^ 64 ≤ a.toNat + x.toNat))
  change (a + x + BitVec.ofNat 64 0).toNat + 2 ^ 64 *
    (decide (2 ^ 64 ≤ a.toNat + x.toNat)).toNat = a.toNat + x.toNat at hl
  rw [VG.Proof.Bignum.AArch64.add_ofNat0] at hl
  rw [boolWord] at hh
  omega_arith

/-- The low/high halves of a diagonal product retain its complete value. -/
theorem square_halves (a : BitVec 64) :
    (a*a).toNat + 2 ^ 64 *
      (BitVec.ofNat 64 (a.toNat*a.toNat / 2 ^ 64)).toNat = a.toNat*a.toNat := by
  have ha := a.isLt
  have hle := Nat.mul_le_mul
    (show a.toNat ≤ 2 ^ 64 - 1 by omega_arith)
    (show a.toNat ≤ 2 ^ 64 - 1 by omega_arith)
  have hq : a.toNat*a.toNat / 2 ^ 64 < 2 ^ 64 := by omega_arith
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  omega_arith

/-- Double a cross-product pair, add the diagonal, then the preceding carry. -/
theorem diagonal_pair_val (al ah x y p : BitVec 64) :
    let c0 := decide (2 ^ 64 ≤ x.toNat + x.toNat)
    let lo0 := x + x
    let hi0 := y + y + BitVec.ofNat 64 c0.toNat
    let e0 := decide (2 ^ 64 ≤ y.toNat + y.toNat + c0.toNat)
    let c1 := decide (2 ^ 64 ≤ lo0.toNat + al.toNat)
    let lo1 := lo0 + al
    let hi1 := hi0 + ah + BitVec.ofNat 64 c1.toNat
    let e1 := decide (2 ^ 64 ≤ hi0.toNat + ah.toNat + c1.toNat)
    let c2 := decide (2 ^ 64 ≤ lo1.toNat + p.toNat)
    let lo2 := lo1 + p
    let hi2 := hi1 + BitVec.ofNat 64 c2.toNat
    let e2 := decide (2 ^ 64 ≤ hi1.toNat + (decide (2 ^ 64 ≤ lo1.toNat + p.toNat)).toNat)
    lo2.toNat + 2 ^ 64 * hi2.toNat +
        2 ^ 128 * (e0.toNat + e1.toNat + e2.toNat) =
      2 * (x.toNat + 2 ^ 64 * y.toNat) + al.toNat + 2 ^ 64*ah.toNat + p.toNat := by
  dsimp only
  let c0 := decide (2 ^ 64 ≤ x.toNat + x.toNat)
  let lo0 := x + x
  let hi0 := y + y + BitVec.ofNat 64 c0.toNat
  let c1 := decide (2 ^ 64 ≤ lo0.toNat + al.toNat)
  let lo1 := lo0 + al
  let hi1 := hi0 + ah + BitVec.ofNat 64 c1.toNat
  have h0 := pair_add_val x y x y
  have h1 := pair_add_val lo0 hi0 al ah
  have h2 := pair_add_val lo1 hi1 p 0
  dsimp only at h0 h1 h2
  simp only [VG.Proof.Bignum.AArch64.add_zero64] at h2
  change _ + 2 ^ 64 * _ + 2 ^ 128 *
    (decide (2 ^ 64 ≤ hi1.toNat + (decide (2 ^ 64 ≤ lo1.toNat + p.toNat)).toNat)).toNat =
    lo1.toNat + 2 ^ 64 * hi1.toNat + p.toNat at h2
  dsimp only [lo1, hi1, c1, lo0, hi0, c0] at h1 h2
  omega_arith

/-- Double a cross-product pair, add the diagonal, then the preceding carry. -/
theorem diagonal_val (a x y p : BitVec 64) :
    let c0 := decide (2 ^ 64 ≤ x.toNat + x.toNat)
    let lo0 := x + x
    let hi0 := y + y + BitVec.ofNat 64 c0.toNat
    let e0 := decide (2 ^ 64 ≤ y.toNat + y.toNat + c0.toNat)
    let al := a*a
    let ah := BitVec.ofNat 64 (a.toNat*a.toNat / 2 ^ 64)
    let c1 := decide (2 ^ 64 ≤ lo0.toNat + al.toNat)
    let lo1 := lo0 + al
    let hi1 := hi0 + ah + BitVec.ofNat 64 c1.toNat
    let e1 := decide (2 ^ 64 ≤ hi0.toNat + ah.toNat + c1.toNat)
    let c2 := decide (2 ^ 64 ≤ lo1.toNat + p.toNat)
    let lo2 := lo1 + p
    let hi2 := hi1 + BitVec.ofNat 64 c2.toNat
    let e2 := decide (2 ^ 64 ≤ hi1.toNat + (decide (2 ^ 64 ≤ lo1.toNat + p.toNat)).toNat)
    lo2.toNat + 2 ^ 64 * hi2.toNat +
        2 ^ 128 * (e0.toNat + e1.toNat + e2.toNat) =
      2 * (x.toNat + 2 ^ 64 * y.toNat) + a.toNat*a.toNat + p.toNat := by
  dsimp only
  let c0 := decide (2 ^ 64 ≤ x.toNat + x.toNat)
  let lo0 := x + x
  let hi0 := y + y + BitVec.ofNat 64 c0.toNat
  let al := a*a
  let ah := BitVec.ofNat 64 (a.toNat*a.toNat / 2 ^ 64)
  let c1 := decide (2 ^ 64 ≤ lo0.toNat + al.toNat)
  let lo1 := lo0 + al
  let hi1 := hi0 + ah + BitVec.ofNat 64 c1.toNat
  have h0 := pair_add_val x y x y
  have h1 := pair_add_val lo0 hi0 al ah
  have h2 := pair_add_val lo1 hi1 p 0
  have hp := square_halves a
  dsimp only at h0 h1 h2
  simp only [VG.Proof.Bignum.AArch64.add_zero64] at h2
  change _ + 2 ^ 64 * _ + 2 ^ 128 *
    (decide (2 ^ 64 ≤ hi1.toNat + (decide (2 ^ 64 ≤ lo1.toNat + p.toNat)).toNat)).toNat =
    lo1.toNat + 2 ^ 64 * hi1.toNat + p.toNat at h2
  dsimp only [lo1, hi1, c1, lo0, hi0, c0, al, ah] at h1 h2
  omega_arith

end VG.Proof.Bignum.AArch64.Square
