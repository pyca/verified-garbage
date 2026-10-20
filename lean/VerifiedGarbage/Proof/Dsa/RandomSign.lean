module

public import VerifiedGarbage.Spec.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bounds for randomized signing

The retry loop advances by the sampler's complete draws, including when a
sampled nonce fails to produce a signature. These bounds justify advancing
within the supplied tape and allocating a finite tape for all attempts.
-/

@[expose] public section

namespace VG.Proof.Dsa
open VG.Spec.Dsa

theorem randomSignLoop_used_le (pLen qLen : Nat) (key digest : List VG.Byte)
    (fuel : Nat) (rand : List VG.Byte) :
    (randomSignLoop pLen qLen key digest fuel rand).used ≤ rand.length := by
  induction fuel generalizing rand with
  | zero => simp [randomSignLoop]
  | succ fuel ih =>
    have hd := Random.sample_used_le (privateKeyBytes pLen qLen key).params.q 128 rand
    simp only [randomSignLoop]
    split
    · exact hd
    · split
      · exact hd
      · have hi := ih (rand.drop (VG.Spec.Dsa.Random.sample
          (privateKeyBytes pLen qLen key).params.q 128 rand).used)
        simp only [List.length_drop] at hi
        simp only
        omega

theorem randomSignLoop_used_budget (pLen qLen : Nat) (key digest : List VG.Byte)
    (fuel : Nat) (rand : List VG.Byte) :
    (randomSignLoop pLen qLen key digest fuel rand).used ≤
      fuel * (128 * VG.Spec.Dsa.Random.drawBytes (privateKeyBytes pLen qLen key).params.q) := by
  induction fuel generalizing rand with
  | zero => simp [randomSignLoop]
  | succ fuel ih =>
    have hd := Random.sample_used_budget (privateKeyBytes pLen qLen key).params.q 128 rand
    simp only [randomSignLoop]
    split
    · simp only
      rw [Nat.succ_mul]
      omega
    · split
      · simp only
        rw [Nat.succ_mul]
        omega
      · have hi := ih (rand.drop (VG.Spec.Dsa.Random.sample
          (privateKeyBytes pLen qLen key).params.q 128 rand).used)
        simp only
        rw [Nat.succ_mul]
        omega

theorem randomSignBytes_used_le (pLen qLen : Nat) (key digest rand : List VG.Byte) :
    (randomSignBytes pLen qLen key digest rand).used ≤ rand.length := by
  simp only [randomSignBytes]
  split
  · exact Nat.zero_le _
  · exact randomSignLoop_used_le _ _ _ _ _ _

/-- A successful randomized result comes from the existing supplied-nonce
signer, with a nonce satisfying the sampler's range check. -/
theorem randomSignLoop_signature (pLen qLen : Nat) (key digest : List VG.Byte)
    (fuel : Nat) (rand signature : List VG.Byte)
    (h : (randomSignLoop pLen qLen key digest fuel rand).signature = some signature) :
    ∃ k, 0 < k ∧ k < (privateKeyBytes pLen qLen key).params.q ∧
      signBytes pLen qLen key (encodeBE qLen k) digest = some signature := by
  induction fuel generalizing rand with
  | zero => simp [randomSignLoop] at h
  | succ fuel ih =>
    simp only [randomSignLoop] at h
    split at h
    · simp at h
    next k hk =>
      split at h
      next sig hs =>
        simp only [Option.some.injEq] at h
        subst sig
        have hr := Random.sample_range _ _ _ _ hk
        exact ⟨k, hr.1, hr.2, hs⟩
      next _ => exact ih _ h

/-- The status word and optional signature always agree. -/
theorem randomSignLoop_success (pLen qLen : Nat) (key digest : List VG.Byte)
    (fuel : Nat) (rand : List VG.Byte) :
    (randomSignLoop pLen qLen key digest fuel rand).status = 1 ↔
      (randomSignLoop pLen qLen key digest fuel rand).signature.isSome = true := by
  induction fuel generalizing rand with
  | zero => simp [randomSignLoop]
  | succ fuel ih =>
    simp only [randomSignLoop]
    split
    · split <;> simp
    · split
      · simp
      · exact ih _

end VG.Proof.Dsa
