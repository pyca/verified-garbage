module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.X86.DivCopy

/-! # Doubling a candidate divisor or quotient without losing a carry -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem doubleWords_ok {s : State} {base : Addr} {size n dst tmp : Nat} (S : Scr s base size)
    (positive : 0 < n) (dstRoom : dst + 4 * n ≤ size) (tmpRoom : tmp + 4 * n ≤ size)
    (apart : dst + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ dst)
    (fits : 2 * val32 s.mem base dst n < 2 ^ (32 * n)) :
    WP isa (doubleWords n dst tmp) s fun t =>
      val32 t.mem base dst n = 2 * val32 s.mem base dst n ∧
      Outs base [(dst, 4 * n), (tmp, 4 * n)] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold doubleWords
  refine WP.seq (WP.mono (chainAddW_ok S positive tmpRoom dstRoom dstRoom apart.symm apart.symm)
    fun a ⟨Oa, carry, Ka⟩ => ?_)
  obtain ⟨c, _, value⟩ := carry
  have exactValue : val32 a.mem base tmp n = 2 * val32 s.mem base dst n := by
    cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at value <;> omega
  refine WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok (S.of_keeps Ka (by decide)) positive tmpRoom dstRoom
    (.inr apart)) fun t ⟨Ot, result, Kt⟩ => ?_
  exact ⟨result.trans exactValue, (Outs.of_outside Oa (by simp)).trans (Outs.of_outside Ot (by simp)), Ka.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
