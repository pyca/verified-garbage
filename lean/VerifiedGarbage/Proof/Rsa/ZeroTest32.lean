module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Mem

/-! # Arithmetic of branchless 32-bit zero tests -/

@[expose] public section
namespace VG.Proof.Rsa

theorem shr31 (y : BitVec 32) : (y >>> 31).toNat = if y.msb then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases h : 2 ^ (32 - 1) ≤ y.toNat
  · rw [decide_eq_true h]; simp only [ite_true]; simp only [Nat.reduceSub] at h; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; simp only [Nat.reduceSub] at h; omega

theorem msb_or_neg (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  have z0 : (0 : BitVec 32).toNat = 0 := rfl
  rw [shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide (x := 0 - x), BitVec.toNat_sub, z0,
    Nat.add_zero]
  have := x.isLt
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have : 2 ^ (32 - 1) ≤ x.toNat ∨ 2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat) % 2 ^ 32 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, ite_false, Bool.or_eq_true, decide_eq_true_eq]
    simp only [this, ite_true]; rfl

theorem zero_test32 (x : BitVec 32) :
    (((((0 : BitVec 32) - x) ||| x) >>> 31) ^^^ (1 : BitVec 32)) = BitVec.ofNat 32 (decide (x = (0 : BitVec 32))).toNat := by
  rw [BitVec.or_comm]
  change ((x ||| (0 - x)) >>> 31) ^^^ (1 : BitVec 32) = _
  rw [msb_or_neg]
  by_cases h : x = 0
  · simp only [h, ite_true, decide_true]; rfl
  · simp only [h, ite_false, decide_false]; rfl

theorem byte_xor_zero32 (a b : VG.Byte) : a.setWidth 32 ^^^ b.setWidth 32 = 0 ↔ a = b := by
  rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have eq := congrArg (BitVec.setWidth 8) h
    simpa using eq
  · rintro rfl; rfl


end VG.Proof.Rsa
