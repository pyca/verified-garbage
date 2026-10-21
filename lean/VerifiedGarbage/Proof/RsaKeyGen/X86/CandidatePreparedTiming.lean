module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateIterationLeak
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Spec.MillerRabin

/-! # Complete prepared testing and export release only the declared primality shape -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.RsaKeyGen VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem test_status_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateTest.code E.width montName mont roundName round)
      (StatusPair E (candidateValue E rBytes) (candidateValue E sBytes)) := by
  intro s t tr ur u z H A B
  have trace := (test_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (iterations_eq v length shape) enough _ _ _ _ _ _ H A B).1
  obtain ⟨VU, RU, WU, FU, KU⟩ := wp_result (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v H.left H.savedLeft enough) A
  obtain ⟨VZ, RZ, WZ, FZ, KZ⟩ := wp_result (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v H.right H.savedRight enough) B
  refine ⟨trace, ⟨H.left.finishReady_after_test v VU WU FU KU, H.right.finishReady_after_test v VZ WZ FZ KZ, ?_⟩,
    result_status_eq v RU RZ shape⟩
  rw [KU.1 .esp (by unfold WitnessStep.clob; decide), KZ.1 .esp (by unfold WitnessStep.clob; decide),
    H.left.input.stack, H.right.input.stack]

theorem prepared_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepareAndTest E.width montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepareAndTest
  exact RelCT.seq (test_status_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough shape)
    (result_trace v)

end VG.Proof.RsaKeyGen.X86.Candidate
