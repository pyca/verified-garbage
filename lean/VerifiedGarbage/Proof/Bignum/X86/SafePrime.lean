module

public import VerifiedGarbage.Proof.Bignum.X86.CheckedPrimePower

/-! # The sanitized factor always supports modular arithmetic -/

@[expose] public section
namespace VG.Proof.Bignum.X86

theorem safePrime_gt_one (m : Nat) : 1 < safePrime m := by
  unfold safePrime
  split
  · next H => exact H.1
  · decide

theorem safePrime_of_valid {m : Nat} (gt : 1 < m) (odd : m % 2 = 1) : safePrime m = m := by
  unfold safePrime
  exact ite_eq_left ⟨gt, odd⟩

end VG.Proof.Bignum.X86
