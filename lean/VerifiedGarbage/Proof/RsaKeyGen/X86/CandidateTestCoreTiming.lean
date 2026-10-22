module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Preparation and all witness rounds share only the specified public iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen VG.Proof.Dsa.X86

def CorePair (P : MillerRabinLoop.Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  VG.X86.Taint.Agree (roundTaint [.edi]) s t ∧ CandidatePrepare.Input P s ∧
    CandidatePrepare.Input (P.withSecret other entropy) t ∧
    P.iterations = (P.withSecret other entropy).iterations

theorem prepare_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid) :
    RelCT isa (CorePair P other entropy) (VG.Impl.RsaKeyGen.X86.Prepare.codeAt P.seed P.g.w name mont)
      (MillerRabinLoop.InitialPair P other entropy) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := Prepare.code_rawAt verified noSp stack v.geometry v.length bound v.seedPos v.seedLt
    _ _ _ _ _ _ ⟨H.1, ⟨P.candidate, H.2.1.prepare⟩, ⟨other, H.2.2.1.prepare⟩⟩ E G
  obtain ⟨U, _, _, _⟩ := wp_result (CandidatePrepare.code_ok verified noSp stack v bound H.2.1) E
  obtain ⟨Z, _, _, _⟩ := wp_result (CandidatePrepare.code_ok verified noSp stack w bound H.2.2.1) G
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩,
    ⟨U.prepared, U.readable, U.entropy, U.randPtr, U.randLength, U.used⟩,
    ⟨Z.prepared, Z.readable, Z.entropy, Z.randPtr, Z.randLength, Z.used⟩, H.2.2.2⟩

theorem core_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid)
    (enough : P.start ≤ P.randLen) :
    RelCT isa (CorePair P other entropy) (VG.Impl.RsaKeyGen.X86.CandidateTest.coreWith P.seed P.checks P.bytes P.words P.g.w montName mont roundName round)
      (Pair P.g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateTest.coreWith
  exact RelCT.seq (prepare_pair montVerified montNoSp montStack v bound w)
    (MillerRabinLoop.code_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v w enough)

end VG.Proof.RsaKeyGen.X86.CandidateTest
