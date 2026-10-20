module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Int.ModEq

/-!
# FFDH and RSA use the same Miller–Rabin round

The FFDH specification lists the possible squares explicitly; RSA's
specification uses the bounded iteration transcribed from BoringSSL. They
accept exactly the same witnesses for every odd candidate >= 3. This bridge
also connects RSA's proved four-bit window algorithm to the FFDH test,
without changing either specification or assuming candidate primality.
-/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec.Rsa (powMod splitTwos)
open VG.Spec.RsaKeyGen (bitLength mrIteration)
open VG.Proof.RsaKeyGen

/-- The exponent of two in p-1 fits in an odd candidate's bit length. -/
private theorem split_bounds {p : Nat} (hp : 3 ≤ p) (hodd : p % 2 = 1) :
    1 ≤ (splitTwos (p - 1)).1 ∧ (splitTwos (p - 1)).1 ≤ bitLength p - 1 := by
  obtain ⟨hN, hm2⟩ := splitTwos_spec (p - 1) (by omega)
  have hm : 0 < (splitTwos (p - 1)).2 := by omega
  constructor
  · by_contra h
    have h0 : (splitTwos (p - 1)).1 = 0 := by omega
    rw [h0, Nat.pow_zero, Nat.mul_one] at hN
    omega
  · have hlt : p < 2 ^ bitLength p := bitLength_lt rfl
    have hpow : 2 ^ (splitTwos (p - 1)).1 ≤ p - 1 := by
      exact (Nat.le_mul_of_pos_left _ hm).trans_eq hN.symm
    have hbound : (splitTwos (p - 1)).1 < bitLength p := by
      by_contra h
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show bitLength p ≤ (splitTwos (p - 1)).1 by omega)
      omega
    omega

/-- RSA's bounded test and FFDH's explicit-square test agree. -/
theorem rsa_round_eq {p : Nat} (a : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1) :
    mrIteration p (splitTwos (p - 1)).1 (splitTwos (p - 1)).2 a = Spec.Ffdh.mrRound p a := by
  obtain ⟨ha, haw⟩ := split_bounds hp hodd
  apply Bool.eq_iff_iff.mpr
  rw [mrIteration_iff hp ha haw]
  simp only [Spec.Ffdh.mrRound, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range]
  let z := powMod a (splitTwos (p - 1)).2 p
  have hz : z < p := by
    dsimp [z]
    rw [VG.Proof.Bignum.powMod_eq]
    exact Nat.mod_lt _ (by omega)
  have he : ∀ j, powMod z (2 ^ j) p = sqIter p z j := by
    intro j
    have h := powMod_pow2 z 1 p (by decide) j
    have h1 : powMod z 1 p = z := by
      rw [VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_eq_of_lt hz]
    simpa only [Nat.one_mul, h1] using h
  dsimp only [z] at he
  simp only [he]

/-- The already proved window algorithm implements FFDH's round. -/
theorem window_round_eq {p W : Nat} (a : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (hE : mrE p < 16 ^ W) :
    (wEnd p (wRun p a (mrE p) W W)).2 = Spec.Ffdh.mrRound p a := by
  rw [wEnd_eq a hp hodd (split_bounds hp hodd).2 hE, rsa_round_eq a hp hodd]

end VG.Proof.Ffdh
