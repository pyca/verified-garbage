module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Prepare

/-! # Prepared arithmetic and the complete blinded loop compose without re-reading entropy -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

def ranges (g : Geometry) : List (Nat × Nat) := Prepare.ranges g ++ MillerRabinLoop.ranges g

theorem core_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State}
    (S : Prepare.Input P.g P.candidate P.capacity P.p s P.seed)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateTest.coreWith P.seed P.checks P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateTest.coreWith
  refine WP.seq (WP.mono (CandidatePrepare.code_ok montVerified montNoSp montStack v bound
    ⟨S, readable, entropy, randPtr, randLength, used⟩) fun a ⟨A, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (MillerRabinLoop.code_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v A.prepared A.readable A.entropy A.randPtr A.randLength A.used enough)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  refine ⟨T, result, ?_, (VG.X86.Frame.below_mono Fa (by decide) v.low).trans Ft, ?_⟩
  · exact (Wa.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  · exact Ka.trans Kt

end VG.Proof.RsaKeyGen.X86.CandidateTest
