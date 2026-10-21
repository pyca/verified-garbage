module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Exhaustion before drawing a candidate returns zero status and zero consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem no_entropy_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateFinish.none s fun t =>
      Outputs E 0 0 (List.replicate E.length 0) t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.none_ok I.scratch (by have H : 256 ≤ E.size := v.geometry.headerFit; omega)
    I.usedWrite I.usedPointer) fun t ⟨statusEq, memory, O, K⟩ => ?_
  refine ⟨⟨statusEq, ?_, ?_⟩, used_frame O, K.mono (by unfold WitnessStep.clob; decide)⟩
  · exact (VG.Proof.Bignum.scratch_bytes O (by have := v.outFit; omega) v.outUsed).trans zeros
  · rw [memory, Mem.readW_writeW_self64]

end VG.Proof.RsaKeyGen.X86.Candidate
