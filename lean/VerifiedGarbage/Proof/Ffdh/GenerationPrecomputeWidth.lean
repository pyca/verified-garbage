module

public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Spec.RsaKeyGen

/-! Recover the exact public exponent width from its saved byte width and mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.ScalarWidth

theorem mask_bitLength (bits : Nat) :
    VG.Spec.RsaKeyGen.bitLength (mask bits).toNat = headBits bits := by
  rw [mask_toNat]
  have bound := (headBits_parts bits).1
  generalize headBits bits = h at *
  have cases : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem recover_bits (bits : Nat) :
    8*(width bits-1)+VG.Spec.RsaKeyGen.bitLength (mask bits).toNat = bits := by
  rw [mask_bitLength]
  exact (headBits_parts bits).2

theorem mask_positive {bits : Nat} (positive : 0<bits) : 0<(mask bits).toNat := by
  have headPositive : 0<headBits bits := by unfold headBits width; omega
  have powBound : 2 ≤ 2^headBits bits :=
    Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) headPositive
  rw [mask_toNat]
  omega

theorem mask_shift {bits : Nat} (positive : 0<bits) :
    ((BitVec.ofNat 32 255) >>> (7-(bits-1)%8)).setWidth 8 = mask bits := by
  have head : headBits bits = (bits-1)%8+1 := by unfold headBits width; omega
  unfold mask
  rw [head]
  have bound : (bits-1)%8<8 := Nat.mod_lt _ (by decide)
  generalize (bits-1)%8 = r at *
  have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem mask_shift32 {bits : Nat} (positive : 0<bits) :
    (BitVec.ofNat 32 255) >>> (7-(bits-1)%8) = (mask bits).setWidth 32 := by
  have head : headBits bits = (bits-1)%8+1 := by unfold headBits width; omega
  unfold mask
  rw [head]
  have bound : (bits-1)%8<8 := Nat.mod_lt _ (by decide)
  generalize (bits-1)%8 = r at *
  have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem mask_shift_count {bits : Nat} (positive : 0<bits) (bound : bits≤8192) :
    (7 : BitVec 32) - ((BitVec.ofNat 32 bits - 1) &&& 7) =
      BitVec.ofNat 32 (7-(bits-1)%8) := by
  have sub : BitVec.ofNat 32 bits-1=BitVec.ofNat 32 (bits-1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have low : BitVec.ofNat 32 (bits-1) &&& 7=BitVec.ofNat 32 ((bits-1)%8) := by
    apply BitVec.eq_of_toNat_eq
    change (((bits-1)%2^32) &&& 7)=((bits-1)%8)%2^32
    rw [Nat.mod_eq_of_lt (by omega : bits-1<2^32)]
    rw [show 7=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [sub,low]
  exact BitVec.ofNat_sub_ofNat_of_le (w := 32) 7 ((bits-1)%8) (by omega) (by omega)

theorem width_eq_ceil {bits : Nat} (positive : 0<bits) : width bits=(bits+7)/8 := by
  unfold width
  omega

end VG.Proof.Ffdh.ScalarWidth
