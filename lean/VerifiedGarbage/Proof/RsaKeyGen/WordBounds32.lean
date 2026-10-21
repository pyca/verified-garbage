module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Narrowing a bounded integer represented by native 32-bit words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.WordBounds32
open VG VG.Proof.Mont

theorem low_eq {m : Mem} {B : Addr} {out small big : Nat} (width : small ≤ big)
    (bound : val32 m B out big < 2 ^ (32 * small)) :
    val32 m B out small = val32 m B out big := by
  have split := val32_append m B out small (big - small)
  rw [Nat.add_sub_of_le width] at split
  have high : val32 m B (out + 4 * small) (big - small) = 0 := by
    by_cases h : val32 m B (out + 4 * small) (big - small) = 0
    · exact h
    · have ge := Nat.mul_le_mul_left (2 ^ (32 * small))
        (show 1 ≤ val32 m B (out + 4 * small) (big - small) by omega)
      rw [Nat.mul_one] at ge
      omega
  rw [high, Nat.mul_zero, Nat.add_zero] at split
  exact split.symm

end VG.Proof.RsaKeyGen.WordBounds32
