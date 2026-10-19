module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Word32

/-! # Masked two-byte candidates for the implicit-rejection length -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc
open VG

def candidate (k : Nat) (a b : Byte) : Nat :=
  (256 * a.toNat + b.toNat) &&& bitMask (k - 11)

theorem candidate_bound {k : Nat} (lower : 64 ≤ k) (upper : k ≤ 1024) (a b : Byte) :
    candidate k a b < 2 ^ 31 := by
  have masked : candidate k a b ≤ bitMask (k - 11) := Nat.and_le_right
  have limit := bitMask_le (by omega : k - 11 ≠ 0)
  omega

theorem altStep_candidate (k : Nat) (CL : List Byte) (al i : Nat) :
    altStep k CL al i =
      let c := candidate k (CL.getD (2 * i) 0) (CL.getD (2 * i + 1) 0)
      if c ≤ k - 11 then c else al := by
  simp only [altStep, candidate, cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod]

theorem le_mask {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 - 1 =
      if b ≤ a then BitVec.allOnes 32 else 0 := by
  have result := Word32.mask_ge ha hb true
  simpa only [ite_true, BitVec.and_allOnes, and_true] using result

end VG.Proof.RsaPkcs1Enc
