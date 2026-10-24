module

import VerifiedGarbage.Proof.Framework.PowLit

public import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding
public import Init.Data.BitVec.Lemmas

/-! Bounded word arithmetic for public scalar recoding. Only the combined
lookahead/carry sum is enumerated; the two operands are not cross-multiplied. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

open VG.Impl.Ed448.WnafWide

def rawDigit (wide : Bool) (sum : Nat) : BitVec 64 :=
  let r := BitVec.ofNat 64 sum &&& BitVec.ofNat 64 (radix wide-1)
  if r &&& 1 = 0 then 0
  else if r &&& BitVec.ofNat 64 (half wide) = 0 then r
  else r - BitVec.ofNat 64 (radix wide)

private theorem rawDigit_sum : ∀ (wide : Bool), ∀ n < 640,
    rawDigit wide n = BitVec.ofInt 64 (digit wide n) := by decide +kernel

theorem rawDigit_ok (wide : Bool) {bits c : Nat} (hb : bits < radix wide) (hc : c ≤ radix wide) :
    rawDigit wide (bits+c+half wide) = BitVec.ofInt 64 (localDigit wide bits c) := by
  have hh : bits+c+half wide < 640 := by
    cases wide <;> simp only [radix, half, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  rw [rawDigit_sum wide _ hh, localDigit, digit_mod]

theorem ofInt_sub (x y : Int) :
    BitVec.ofInt 64 (x-y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem rawCarry_ok (wide : Bool) {bits c : Nat} (hb : bits < radix wide) (hc : c ≤ radix wide) :
    (BitVec.ofNat 64 c + BitVec.ofNat 64 (bits%2) + BitVec.ofNat 64 (half wide) -
      rawDigit wide (bits+c+half wide)) >>> 1 = BitVec.ofNat 64 (carryNext wide bits c) := by
  rw [rawDigit_ok wide hb hc]
  let n : Int := (c : Int) + (bits%2 : Nat) + half wide - localDigit wide bits c
  have hd := digit_bounds wide ((bits+c+half wide)%radix wide)
  change -(half wide : Int) < localDigit wide bits c ∧ localDigit wide bits c < half wide at hd
  have h0 : 0 ≤ n := by dsimp only [n]; omega
  have hN : n.toNat < 640 := by
    dsimp only [n]
    cases wide <;> simp only [half, radix, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have hw : BitVec.ofNat 64 c + BitVec.ofNat 64 (bits%2) + BitVec.ofNat 64 (half wide) -
      BitVec.ofInt 64 (localDigit wide bits c) = BitVec.ofNat 64 n.toNat := by
    have he := ofInt_sub ((c : Int) + (bits%2 : Nat) + half wide) (localDigit wide bits c)
    simp only [BitVec.ofInt_add, BitVec.ofInt_natCast] at he
    rw [← he]
    change BitVec.ofInt 64 n = BitVec.ofNat 64 n.toNat
    rw [← Int.toNat_of_nonneg h0, BitVec.ofInt_natCast]
    rfl
  rw [hw]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hn64 : n.toNat < 2^64 := by omega
  have hn2 : n.toNat / 2 < 2^64 := by omega
  have eq : carryNext wide bits c = n.toNat / 2 := by
    unfold carryNext n
    congr 2
    omega
  rw [Nat.mod_eq_of_lt hn64, eq, Nat.mod_eq_of_lt hn2]

end VG.Proof.Ed448.WnafWide
