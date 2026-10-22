module

public import VerifiedGarbage.Proof.Weierstrass.Words

/-! # Parity of a canonical field element in a little-endian workspace -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed

open VG VG.Proof.Weierstrass VG.Proof.Mont

/-- The low bit of the little-endian slot is the parity of its canonical
integer, even for encodings whose top word is only partly occupied. -/
theorem word_parity (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    word m base a &&& 1 = BitVec.ofNat 64 (wordsVal m base a n % 2) := by
  have hp : wordsVal m base a n % 2 = (word m base a).toNat % 2 := by
    cases n with
    | zero => omega
    | succ n =>
      simp only [wordsVal, Nat.add_mod, Nat.mul_mod,
        show 2 ^ 64 % 2 = 0 from rfl, Nat.zero_mul, Nat.add_zero, Nat.mod_mod]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat, hp,
    Nat.mod_eq_of_lt (show (word m base a).toNat % 2 < 2 ^ 64 by omega)]

theorem tag_byte (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) (b : Bool) :
    ((((word m base a &&& 1) + 2) &&& (if b then BitVec.allOnes 64 else 0)).setWidth 8) =
      if b then BitVec.ofNat 8 (2 + wordsVal m base a n % 2) else 0 := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [word_parity m base a n hn,
      show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
      BitVec.ofNat_add_ofNat, BitVec.setWidth_ofNat_of_le (by decide), Nat.add_comm]

theorem slot_parity (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    (word m base a).toNat % 2 = wordsVal m base a n % 2 := by
  have h := congrArg BitVec.toNat (word_parity m base a n hn)
  simpa only [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show wordsVal m base a n % 2 < 2 ^ 64 by omega)] using h


theorem xor_low_mask (x y : BitVec 64) :
    0 - ((x ^^^ y) &&& 1) = mask (x.toNat % 2 ≠ y.toNat % 2) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, mask]


theorem readW_low32 (m : Mem) (a : Addr) :
    (m.readW a 64).setWidth 32 = m.readW a 32 := by
  symm
  have e := Mem.read_eq_of_bytes (n := 4) (v := (m.readW a 64).setWidth 32) (a := a) (m := m) fun i hi => by
    rw [BitVec.extractLsb'_setWidth_of_le (by omega)]
    show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * i) 8
    rw [BitVec.extractLsb'_setWidth_of_le (by omega), Mem.extractLsb'_read m a (by omega : i < 8)]
  show (m.read a 4).setWidth 32 = _
  rw [e]; exact BitVec.setWidth_eq _

theorem word32_parity (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    m.readW (off base a) 32 &&& 1 = BitVec.ofNat 32 (wordsVal m base a n % 2) := by
  have h := congrArg (BitVec.setWidth 32) (word_parity m base a n hn)
  simpa only [BitVec.setWidth_and, word, readW_low32, show (1 : BitVec 64).setWidth 32 = 1 from rfl, BitVec.setWidth_ofNat_of_le (show 32 ≤ 64 by decide)] using h

theorem slot32_parity (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    (m.readW (off base a) 32).toNat % 2 = wordsVal m base a n % 2 := by
  have h := congrArg BitVec.toNat (word32_parity m base a n hn)
  simpa only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show wordsVal m base a n % 2 < 2 ^ 32 by omega)] using h

end VG.Proof.EcKey.Compressed
