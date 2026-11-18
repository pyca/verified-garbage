module

import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding
public import Init.Data.BitVec.Lemmas
import VerifiedGarbage.Proof.Framework.Omega
public import Init.Data.Nat.Bitwise.Lemmas

/-! ### `Ed448.WnafWide.Bits`, which the modules that import this one used -/

section

/-! The bounded lookahead reconstructed from expanded scalar bits. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

def bit (k i : Nat) : Nat := k / 2^i % 2

def look (k i n : Nat) : Nat := k / 2^i % 2^n

theorem bit_lt (k i : Nat) : bit k i < 2 := Nat.mod_lt _ (by decide)

theorem look_zero (k i : Nat) : look k i 0 = 0 := by
  simp only [look, Nat.pow_zero, Nat.mod_one]

theorem look_succ (k i n : Nat) :
    look k i (n+1) = look k i n + 2^n * bit k (i+n) := by
  simp only [look, bit]
  rw [Nat.mod_pow_succ, Nat.pow_add, ← Nat.div_div_eq_div_mul]

theorem look_step (k i n a : Nat) :
    (a*2+bit k (i+n))*2^n + look k i n = a*2^(n+1) + look k i (n+1) := by
  rw [look_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 2 (2^n), ← Nat.mul_assoc]
  have hc := Nat.mul_comm (2^n) (bit k (i+n))
  omega_using [hc]

theorem bit_shift (k i : Nat) : (k >>> i) &&& 1 = bit k i := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rfl

end VG.Proof.Ed448.WnafWide

end

end

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
    cases wide <;> simp only [radix, half, Bool.false_eq_true, ↓reduceIte] at * <;> omega_using [hb, hc]
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
  have h0 : 0 ≤ n := by dsimp only [n]; omega_using [hd]
  have hN : n.toNat < 640 := by
    dsimp only [n]
    cases wide <;> simp only [half, radix, Bool.false_eq_true, ↓reduceIte] at * <;> omega_using [hc, hd]
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
  have hn64 : n.toNat < 2^64 := by omega_using [hN]
  have hn2 : n.toNat / 2 < 2^64 := by omega_using [hN]
  have eq : carryNext wide bits c = n.toNat / 2 := by
    unfold carryNext n
    congr 2
    omega_using []
  rw [Nat.mod_eq_of_lt hn64, eq, Nat.mod_eq_of_lt hn2]

end VG.Proof.Ed448.WnafWide
