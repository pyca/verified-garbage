module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEntry
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultSpec

/-! # Native argument entry and the complete candidate body satisfy the shared operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

structure EntryInput (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop where
  arguments : CandidateArgs.Entry E.base E.size E.p E.argument s
  outWrite : InRegions s.wr (E.out.setWidth 64) E.length
  usedWrite : VG.Proof.Mont.X86.Rt.Ws s (E.used.setWidth 64) 8
  memory : MemoryFacts E eBytes pBytes entropy s

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem enter_input_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateArgs.enter s fun t =>
      Input E eBytes pBytes entropy t ∧ WorkFrame E s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  refine WP.mono_syms (CandidateArgs.enter_ok I.arguments) fun t ⟨C, header, used, O, K⟩ syms => ?_
  have F : Frame [E.workspaceRegion] s.mem t.mem :=
    workspaceGlobalFrame (g := E.geometry) (Outs.of_outside O List.mem_cons_self)
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 0 + 48 ≤ E.size; have := v.geometry.headerFit; change 256 ≤ E.size at this; omega)
  have frame : WorkFrame E s.mem t.mem := F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)
  exact ⟨⟨C.scratch, C.sp, header, used, by rw [K.2.2]; exact I.outWrite,
    I.usedWrite.of_keeps K, I.memory.keep v K frame (by rw [syms])⟩, frame, K⟩

theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) s fun t =>
      StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps bodyClob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.body
  refine WP.seq (WP.mono (enter_input_ok v I) fun a ⟨Ia, F, K⟩ => ?_)
  refine WP.mono (front_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Ia)
    fun t ⟨output, Ft, Kt⟩ => ?_
  exact ⟨output, F.mutable.trans Ft, (K.mono (by unfold bodyClob; decide)).trans
    (Kt.mono (by unfold WitnessStep.clob bodyClob; decide))⟩

end VG.Proof.RsaKeyGen.X86.Candidate
