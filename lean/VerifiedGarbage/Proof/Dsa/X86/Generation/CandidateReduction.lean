module
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Rsa.WordRanges
import VerifiedGarbage.Proof.Framework.Mem
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateDivision
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateDouble
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateSubtract
import VerifiedGarbage.Proof.Rsa.X86.DivCopy

/-! # One division produces both the p candidate and its generator exponent -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def candidateWrites (n : Nat) : List (Nat × Nat) :=
  [(candidateQuotient, 4 * n), (candidateRemainder, 4 * (n + 1)), (candidateTemporary, 4 * (n + 1)),
   (candidateOriginal, 4 * n), (candidateP, 4 * n)]

theorem candidateReduction_ok {s : State} {base : Addr} {size n x q : Nat} (S : Scr s base size)
    (positive : 0 < n) (width : n ≤ 96) (room : 3072 ≤ size)
    (qpos : 0 < q) (qbound : 2 * q < 2 ^ (32 * n))
    (original : val32 s.mem base candidateQuotient n = x)
    (divisor : val32 s.mem base candidateDivisor (n + 1) = 2 * q) :
    WP isa (reduceCandidate n) s fun t =>
      val32 t.mem base candidateP n = x + 1 - x % (2 * q) ∧
      val32 t.mem base candidateQuotient n = (x + 1 - x % (2 * q) - 1) / q ∧
      Outs base (candidateWrites n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have bound := S.nowrap
  have xbound : x < 2 ^ (32 * n) := original ▸ val32_lt s.mem base candidateQuotient n
  unfold reduceCandidate
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok S positive
    (src := candidateQuotient) (dst := candidateOriginal)
    (by unfold candidateQuotient; omega) (by unfold candidateOriginal; omega)
    (.inr (.inr (by unfold candidateQuotient candidateOriginal; omega))))
    fun a ⟨Oa, saved, Ka⟩ => ?_)
  have originala : val32 a.mem base candidateQuotient n = x := by
    rw [Oa.val32 (by unfold candidateOriginal candidateQuotient; omega) (by unfold candidateQuotient; omega), original]
  have divisora : val32 a.mem base candidateDivisor (n + 1) = 2 * q := by
    rw [Oa.val32 (by unfold candidateOriginal candidateDivisor; omega) (by unfold candidateDivisor; omega), divisor]
  refine WP.seq (WP.mono (candidateDivision_ok (S.of_keeps Ka (by decide)) positive width (by omega)
    qpos qbound originala divisora) fun b ⟨rem, quotient, Ob, Kb⟩ => ?_)
  have savedb : val32 b.mem base candidateOriginal n = x := by
    rw [Ob.val32 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [candidateQuotient, candidateRemainder, candidateTemporary, candidateOriginal] <;> omega)
      (by unfold candidateOriginal; omega), saved, original]
  have Ksb : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s b := (Ka.mono (by decide)).trans Kb
  refine WP.seq (WP.mono (candidateSubtract_ok (S.of_keeps Ksb (by decide)) positive width room qpos qbound savedb rem)
    fun c ⟨pc, Oc, Kc⟩ => ?_)
  have quotientc : val32 c.mem base candidateQuotient n = x / (2 * q) := by
    rw [Oc.val32 (by unfold candidateP candidateQuotient; omega) (by unfold candidateQuotient; omega), quotient]
  have Ksc := Ksb.trans (Kc.mono (by decide))
  have fits : 2 * val32 c.mem base candidateQuotient n < 2 ^ (32 * n) := by
    rw [quotientc]
    have h := Nat.mul_le_mul_right (x / (2 * q)) (show 2 ≤ 2 * q by omega)
    have j := Nat.mul_div_le x (2 * q)
    omega
  refine WP.mono (doubleWords_ok (S.of_keeps Ksc (by decide)) positive
    (dst := candidateQuotient) (tmp := candidateTemporary)
    (by unfold candidateQuotient; omega) (by unfold candidateTemporary; omega)
    (.inl (by unfold candidateQuotient candidateTemporary; omega)) fits)
    fun t ⟨exponent, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, Ksc.trans (Kt.mono (by decide))⟩
  · rw [Ot.val32 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [candidateQuotient, candidateTemporary, candidateP] <;> omega)
      (by unfold candidateP; omega), pc]
  · rw [exponent, quotientc, VG.Proof.Dsa.Generation.pReduction_generatorExponent x qpos]
  · have A : Outs base (candidateWrites n) s.mem a.mem := Outs.of_outside Oa (by simp [candidateWrites])
    have B : Outs base (candidateWrites n) a.mem b.mem := Ob.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [candidateWrites])
    have C : Outs base (candidateWrites n) b.mem c.mem := Outs.of_outside Oc (by simp [candidateWrites])
    have T : Outs base (candidateWrites n) c.mem t.mem := by
      apply VG.Proof.Rsa.outs_cover Ot
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp [candidateWrites], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(candidateTemporary, 4 * (n + 1)), by simp [candidateWrites], Nat.le_refl _, by omega⟩
    exact ((A.trans B).trans C).trans T
end VG.Proof.Dsa.X86.Generation
