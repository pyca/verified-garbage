module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialLoopState

/-! Every packed table entry satisfies the native prime-test preconditions. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

theorem TrialMachine.table_prime {P : TrialPlan} {initial s : State} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial P.base P.bytes sp values s)
    {i : Nat} (hi : i < 1024) (prime : s.gpr .ebx = BitVec.ofNat 32 (tabEntry i))
    (start : values 0 = P.start) (last : values 1 = P.start + BitVec.ofNat 32 (8 * P.width)) :
    WP isa (trialPrime trialStart trialEnd) s fun t =>
      TrialMachine initial P.base P.bytes sp values t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (P.number initial % tabEntry i = 0)).toNat := by
  have facts := tabEntry_facts hi
  have reg : (s.gpr .ebx).toNat = tabEntry i := by
    rw [prime, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bound : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162 := by
    rw [reg]; exact facts.2
  have odd : (s.gpr .ebx).toNat % 2 = 1 := by rw [reg]; exact facts.1
  refine WP.mono (h.prime (ptr := P.start) (offset := P.candidate) (w := P.width)
    rfl P.candidateFits P.widthSmall P.widthPositive bound odd start last) ?_
  rintro t ⟨ht, value⟩
  rw [reg] at value
  exact ⟨ht, value⟩

theorem trial_count_word {count k : Nat} (step : k < count) :
    BitVec.ofNat 32 (count - k) - 1 = BitVec.ofNat 32 (count - (k + 1)) := by
  change BitVec.ofNat 32 (count - k) - BitVec.ofNat 32 1 = _
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  congr 1

theorem trial_count_flag {count k : Nat} (bound : count ≤ 512) (step : k < count) :
    (BitVec.ofNat 32 (count - (k + 1)) == 0) = decide (k + 1 = count) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
    change count - (k + 1) = 0 at h
    omega
  · intro eq
    rw [eq, Nat.sub_self]
    rfl

end VG.Proof.Dsa.X86.Generation
