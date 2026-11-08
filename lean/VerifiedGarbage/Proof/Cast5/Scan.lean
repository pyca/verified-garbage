module

public import VerifiedGarbage.Proof.Cast5.Table

/-! # Constant-time CAST5 table scans: lane selection in groups of four -/

@[expose] public section

namespace VG.Proof.Cast5

open VG

/-- Lane `k` of the result once entries `0 … j - 1` are visited. -/
def acc (m : Mem) (T : Addr) (idx : Nat → BitVec 32) (j k : Nat) : BitVec 32 :=
  if (idx k).toNat < j then ent m T (idx k).toNat k else 0

/-- Every lane `n`. -/
def splat (n : Nat) : Nat → BitVec 32 := fun _ => BitVec.ofNat 32 n

theorem zero_or' (y : BitVec 32) : 0 ||| y = y := BitVec.eq_of_getLsbD_eq (by simp)
theorem or_zero' (y : BitVec 32) : y ||| 0 = y := BitVec.eq_of_getLsbD_eq (by simp)
theorem and_zero' (y : BitVec 32) : y &&& 0 = 0 := BitVec.eq_of_getLsbD_eq (by simp)
theorem and_ones' (y : BitVec 32) : y &&& 0xFFFFFFFF = y := by
  rw [show (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

/-- A replicated mask for the low bit, without a branch. -/
def bitMask (x : BitVec 32) : BitVec 32 := 0 - (x &&& 1)

def mux (a b mask : BitVec 32) : BitVec 32 := a ^^^ ((b ^^^ a) &&& mask)

theorem mux_bit (a b x : BitVec 32) :
    mux a b (bitMask x) = if x.toNat % 2 = 0 then a else b := by
  have hn : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  unfold mux bitMask
  by_cases h : x.toNat % 2 = 0
  · have hv : x &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)
    rw [hv, ite_eq_left h]
    simp only [BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]
  · have hv : x &&& 1 = 1 := BitVec.eq_of_toNat_eq (by change (x &&& 1).toNat = 1; rw [hn]; have := Nat.mod_lt x.toNat (by decide : 0 < 2); omega)
    rw [hv, ite_eq_right h, show (0 - (1 : BitVec 32)) = BitVec.allOnes 32 by rfl,
      BitVec.and_allOnes, BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Selecting one of four adjacent entries in each lane. -/
def tileVal (m : Mem) (T : Addr) (i : BitVec 32) (q k : Nat) : BitVec 32 :=
  mux (mux (ent m T (4 * q) k) (ent m T (4 * q + 1) k) (bitMask i))
    (mux (ent m T (4 * q + 2) k) (ent m T (4 * q + 3) k) (bitMask i)) (bitMask (i >>> 1))

theorem acc_tile (m : Mem) (T : Addr) (idx : Nat → BitVec 32) {q : Nat} (hq : q < 64) (k : Nat) :
    acc m T idx (4 * q) k |||
      (tileVal m T (idx k) q k &&& if idx k >>> 2 = BitVec.ofNat 32 q then 0xffffffff else 0) =
      acc m T idx (4 * (q + 1)) k := by
  have hn : (idx k >>> 2).toNat = (idx k).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases he : idx k >>> 2 = BitVec.ofNat 32 q
  · have hdiv : (idx k).toNat / 4 = q := by
      have h := congrArg BitVec.toNat he
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
      exact h
    have hold : ¬ (idx k).toNat < 4 * q := by omega
    have hnew : (idx k).toNat < 4 * (q + 1) := by omega
    simp only [acc, ite_eq_right hold, ite_eq_left hnew, ite_eq_left he, and_ones', zero_or']
    unfold tileVal
    rw [mux_bit, mux_bit, mux_bit]
    have hs : (idx k >>> 1).toNat = (idx k).toNat / 2 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hs]
    rcases (show (idx k).toNat % 4 = 0 ∨ (idx k).toNat % 4 = 1 ∨
      (idx k).toNat % 4 = 2 ∨ (idx k).toNat % 4 = 3 by omega) with h | h | h | h
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), show (idx k).toNat = 4 * q by omega]
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), show (idx k).toNat = 4 * q + 1 by omega]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), show (idx k).toNat = 4 * q + 2 by omega]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), show (idx k).toNat = 4 * q + 3 by omega]
  · have hdiv : (idx k).toNat / 4 ≠ q := by
      intro h
      apply he
      apply BitVec.eq_of_toNat_eq
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), h]
    rw [ite_eq_right he, and_zero', or_zero']
    unfold acc
    by_cases h : (idx k).toNat < 4 * q
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

end VG.Proof.Cast5
