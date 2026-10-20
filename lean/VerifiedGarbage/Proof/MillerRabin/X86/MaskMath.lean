module

import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # The fixed-window digit comparison produces an all-ones selection mask -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG.Proof.MillerRabin.Word32

theorem digit_lt (x : BitVec 32) : (x >>> 28).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem digitMask (x : BitVec 32) {j : Nat} (index : j < 16) :
    0#32 - ((((x >>> 28) ^^^ BitVec.ofNat 32 j) - 1) >>> 31) =
      if (x >>> 28).toNat = j then BitVec.allOnes 32 else 0#32 := by
  have h := mask_eq (x >>> 28).toNat (digit_lt x) j index
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  have bit : ((((x >>> 28) ^^^ BitVec.ofNat 32 j) - 1) >>> 31) =
      BitVec.ofNat 32 (decide ((x >>> 28).toNat = j)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [h]
    cases decide ((x >>> 28).toNat = j) <;> rfl
  rw [bit]
  by_cases eq : (x >>> 28).toNat = j <;> simp only [eq, decide_true, decide_false, ↓reduceIte] <;> rfl

end VG.Proof.MillerRabin.X86
