module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep

/-! # Prepared testing and finish implement exactly the complete primality result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def PrimalityOutputs (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop :=
  match Spec.RsaKeyGen.primalityTest c (entropy.drop E.length) with
  | none => Outputs E 0 0 (List.replicate E.length 0) s
  | some (prime, rest) => Outputs E (if prime then 1 else 3) (entropy.length - rest.length)
      (if prime then Spec.Rsa.i2osp c E.length else List.replicate E.length 0) s

/-- Miller–Rabin's result is the same code at every width. -/
theorem mrResult_zero (w : Nat) :
    VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult 0 = VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult w := by
  simp only [VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult, VG.Impl.RsaKeyGen.X86.CandidateFinish.prime,
    VG.Proof.RsaKeyGen.X86.ExponentRt.slot0_eq]

/-- Preparation with the exponent at the run-time width, the witnesses, and
the result. -/
theorem tested_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) s fun t =>
      PrimalityOutputs E (candidateValue E entropy) entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.tested
  rw [mrResult_zero E.width]
  refine WP.seq (WP.mono (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v D minusOne enough)
    fun a ⟨value, result, W, F, K⟩ => ?_)
  have ready := D.finishReady_after_test v value W F K
  have frame : MutableFrame E s.mem a.mem := F.mutable
  rw [MillerRabinLoop.Result, v.test_eq] at result
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop (8 * E.width)) with
    | none => w32 a.mem E.base 168 = 0
    | some (prime, rest) => w32 a.mem E.base 168 = (if prime then 1 else 3) ∧
        w32 a.mem E.base 152 = entropy.length - rest.length) at result
  rw [v.length_eq] at result
  cases test : Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length) with
  | none =>
    rw [test] at result
    refine WP.mono (finish_result_ok v ready (Or.inl rfl) result) fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩
  | some pr =>
    obtain ⟨prime, rest⟩ := pr
    rw [test] at result
    cases prime
    · refine WP.mono (finish_result_ok v ready (Or.inr (Or.inr rfl)) result.1) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [ResultOutputs, result.2] at output
      exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩
    · refine WP.mono (finish_result_ok v ready (Or.inr (Or.inl rfl)) result.1) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [ResultOutputs, result.2] at output
      exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
