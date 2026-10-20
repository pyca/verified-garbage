module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitStores
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration

/-! The native 32-bit halves encode the shared 64-bit controller values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem shiftedPair (x : BitVec 32) :
    ((x >>> 26) ++ (x <<< 6) : BitVec 64).toNat = x.toNat * 64 := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (x <<< 6).isLt]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show 2 ^ 6 = 64 by rfl, show 2 ^ 32 = 2 ^ 26 * 64 by rfl, Nat.mul_mod_mul_right]
  have := Nat.mod_add_div x.toNat (2 ^ 26)
  omega

theorem zeroHigh (x : BitVec 32) :
    ((0 : BitVec 32) ++ x : BitVec 64) = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx64 : x.toNat < 2 ^ 64 := by have := x.isLt; omega
  simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]

theorem keyInitValues_words (m : Mem) (B : Addr) (k : BitVec 32) :
    Spec.Rsa.wordsAt (controlMem m B (keyInitValues k)) B 4 =
      [128, 128, BitVec.ofNat 64 k.toNat, BitVec.ofNat 64 k.toNat] := by
  rw [controlMem_words]
  simp only [keyInitValues, zeroHigh]
  rfl

theorem parameterInitValues_words (m : Mem) (B : Addr) (bits : BitVec 32)
    (bound : bits.toNat ≤ 8192) :
    Spec.Rsa.wordsAt (controlMem m B (parameterInitValues bits)) B 4 =
      [BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits.toNat),
       BitVec.ofNat 64 ((bits.toNat + 7) / 8),
       BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits.toNat),
       BitVec.ofNat 64 (512 * ((bits.toNat + 7) / 8))] := by
  rw [controlMem_words]
  have squareBound := Nat.mul_le_mul bound bound
  have square : (bits * bits).toNat = bits.toNat * bits.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have width : ((bits + 7) >>> 3).toNat = (bits.toNat + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
    simp only [show (7 : BitVec 32).toNat = 7 from rfl, show 2 ^ 3 = 8 from rfl,
      Nat.mod_eq_of_lt (by omega : bits.toNat + 7 < 2 ^ 32)]
  have widthBound : (bits.toNat + 7) / 8 ≤ 1024 := by omega
  have entropy : (((bits + 7) >>> 3) + (((bits + 7) >>> 3) <<< 15)).toNat =
      32769 * ((bits.toNat + 7) / 8) := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, width]
    have shiftBound : (bits.toNat + 7) / 8 * 2 ^ 15 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt shiftBound, Nat.mod_eq_of_lt (by omega)]
    omega
  have request : (((bits + 7) >>> 3) <<< 9).toNat = 512 * ((bits.toNat + 7) / 8) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, width, Nat.mod_eq_of_lt (by omega)]
    omega
  have budget : (((bits * bits) >>> 26) ++ ((bits * bits) <<< 6) : BitVec 64) =
      BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [shiftedPair, square, BitVec.toNat_ofNat]
    simp only [Spec.Ffdh.parameterAttempts, Nat.mod_eq_of_lt (by omega : bits.toNat * bits.toNat * 64 < 2 ^ 64)]
  simp only [parameterInitValues, zeroHigh, budget, width, entropy, request, Spec.Ffdh.parameterEntropy]

end VG.Proof.Ffdh.Arm
