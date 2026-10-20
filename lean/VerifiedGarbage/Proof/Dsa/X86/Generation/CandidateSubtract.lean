module
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateIncrement
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Turn the division remainder into the exact odd p candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem candidate_low_words {mem : Mem} {base : Addr} {offset n value : Nat}
    (full : val32 mem base offset (n + 1) = value) (fits : value < 2 ^ (32 * n)) :
    val32 mem base offset n = value := by
  have low := val32_lt mem base offset n
  rw [val32_succ] at full
  have modulus := congrArg (fun v => v % 2 ^ (32 * n)) full
  simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt low, Nat.mod_eq_of_lt fits] using modulus

theorem candidateSubtract_ok {s : State} {base : Addr} {size n x q : Nat} (S : Scr s base size)
    (positive : 0 < n) (width : n ≤ 96) (room : 3072 ≤ size)
    (qpos : 0 < q) (qbound : 2 * q < 2 ^ (32 * n))
    (original : val32 s.mem base candidateOriginal n = x)
    (remainder : val32 s.mem base candidateRemainder (n + 1) = x % (2 * q)) :
    WP isa (.seq (chainW .sbb n candidateP candidateOriginal candidateRemainder)
      (.block (incrementEven candidateP))) s fun t =>
      val32 t.mem base candidateP n = x + 1 - x % (2 * q) ∧
      Outside base candidateP (4 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have remBound : x % (2 * q) < 2 ^ (32 * n) := Nat.lt_trans (Nat.mod_lt _ (by omega)) qbound
  have remLow := candidate_low_words remainder remBound
  have xbound : x < 2 ^ (32 * n) := original ▸ val32_lt s.mem base candidateOriginal n
  have remLe := Nat.mod_le x (2 * q)
  refine WP.seq (WP.mono (chainSubW_ok S positive
    (o := candidateP) (a := candidateOriginal) (b := candidateRemainder)
    (by unfold candidateP; omega) (by unfold candidateOriginal; omega) (by unfold candidateRemainder; omega)
    (.inr (by unfold candidateP candidateOriginal; omega)) (.inr (by unfold candidateP candidateRemainder; omega)))
    fun a ⟨Oa, carry, Ka⟩ => ?_)
  obtain ⟨c, _, value⟩ := carry
  rw [original, remLow] at value
  have result : val32 a.mem base candidateP n = x - x % (2 * q) := by
    have bound := val32_lt a.mem base candidateP n
    cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at value <;> omega
  have even : val32 a.mem base candidateP n % 2 = 0 := by
    have h := VG.Proof.Dsa.Generation.pReduction_odd x q
    rw [VG.Proof.Dsa.Generation.pReduction_sub] at h
    rw [result]
    omega
  refine WP.mono (incrementEven_ok (S.of_keeps Ka (by decide)) positive (by unfold candidateP; omega) even)
    fun t ⟨increment, Ot, Kt⟩ => ?_
  exact ⟨by rw [increment, result, VG.Proof.Dsa.Generation.pReduction_sub],
    Oa.trans (Ot.mono (by omega) (by omega)), Ka.trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
