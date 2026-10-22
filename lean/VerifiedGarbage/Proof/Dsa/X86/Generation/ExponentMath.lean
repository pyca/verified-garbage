module

public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow

/-! Word operations for the existing four-bit Miller–Rabin exponent. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation

def sigmaWord (t : BitVec 32) : BitVec 32 := ((t - 1) &&& 3) + 1

theorem sigma_word_value (t : BitVec 32) : (sigmaWord t).toNat = VG.Proof.RsaKeyGen.sigOf t.toNat := by
  have bound := t.isLt
  unfold sigmaWord VG.Proof.RsaKeyGen.sigOf
  rw [BitVec.toNat_add, BitVec.toNat_and, show (3 : BitVec 32).toNat = 2 ^ 2 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_sub,
    show (1 : BitVec 32).toNat = 1 by rfl]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 32)]
  split <;> omega

def greaterWord (sigma : BitVec 32) (threshold : Nat) : BitVec 32 :=
  ((sigma - BitVec.ofNat 32 (threshold + 1)) >>> 31) ^^^ 1

theorem greater_word_value {sigma threshold : Nat} (hs : 1 ≤ sigma ∧ sigma ≤ 4)
    (ht : 1 ≤ threshold ∧ threshold ≤ 3) :
    greaterWord (BitVec.ofNat 32 sigma) threshold = BitVec.ofNat 32 (decide (threshold < sigma)).toNat := by
  rcases (by omega : sigma = 1 ∨ sigma = 2 ∨ sigma = 3 ∨ sigma = 4) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : threshold = 1 ∨ threshold = 2 ∨ threshold = 3) with rfl | rfl | rfl <;> decide

end VG.Proof.Dsa.X86.Generation
