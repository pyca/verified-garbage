module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEntry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultSpec

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClearInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
/-! # Native argument entry and the complete candidate body satisfy the shared operation -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateAvailable.lean`, which only this module imported.
section

/-! # The candidate drawn and filtered at its run-time width, then tested -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Outputs.keepFlags {E : Environment} {status count : Nat} {bytes : List Byte} {s t : State}
    (O : Outputs E status count bytes s) (F : Fupd s t) : Outputs E status count bytes t := by
  unfold Outputs at O ⊢
  rw [F.gpr, F.mem]
  exact O

theorem available_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round) s fun t =>
      FilteredOutputs E (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available
  refine WP.seq (WP.mono (front_rt_ok v I zeros enough) fun d ⟨front, Fd, Kd⟩ => ?_)
  refine WP.seq (wp_cmpS rfl fun e Ee Z => WP.block_nil ?_)
  have Fe : MutableFrame E s.mem e.mem := by rw [Ee.mem]; exact Fd
  have Ke : Keeps WitnessStep.clob s e := Kd.widen (Ee.keeps [])
  unfold FrontOutputs at front
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)
  · rw [close] at front
    simp only [Bool.false_eq_true, ↓reduceIte] at front
    cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · rw [composite] at front
      simp only [Bool.false_eq_true, ↓reduceIte] at front
      obtain ⟨De, four⟩ := front
      refine WP.ite true (by change e.zf = _; rw [Z, four]; rfl) (fun _ => ?_) (fun bad => nomatch bad)
      have Dd := De.keepMem v Ee.mem (Ee.keeps []) (by decide) (by decide) Ee.syms
      refine WP.mono (exponent_result_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Dd enough)
        fun t ⟨output, Ft, Kt⟩ => ?_
      exact ⟨by simpa only [FilteredOutputs, SieveOutputs, close, composite, Bool.false_eq_true, ↓reduceIte]
        using output, Fe.trans Ft, Ke.trans Kt⟩
    · rw [composite] at front
      simp only [↓reduceIte] at front
      refine WP.ite false (by change e.zf = _; rw [Z, front.1]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.block_nil ⟨?_, Fe, Ke⟩
      simpa only [FilteredOutputs, SieveOutputs, close, composite, Bool.false_eq_true, ↓reduceIte] using
        front.keepFlags Ee
  · rw [close] at front
    simp only [↓reduceIte] at front
    refine WP.ite false (by change e.zf = _; rw [Z, front.1]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.block_nil ⟨?_, Fe, Ke⟩
    simpa only [FilteredOutputs, close, ↓reduceIte] using front.keepFlags Ee

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateNoEntropy.lean`, which only this module imported.
section

/-! # Exhaustion before drawing a candidate returns zero status and zero consumption -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFront.lean`, which only this module imported.
section

/-! # Clearing, the public entropy guard, and width dispatch implement the candidate operation -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem front_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) :
    WP isa (.seq VG.Impl.RsaKeyGen.X86.Candidate.clear
      (.seq (.block [.mov .eax (.mem (sc 32)), .alu .cmp .eax (.mem (sc 4))])
        (.ite .b VG.Impl.RsaKeyGen.X86.CandidateFinish.none
          (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round)))) s fun t =>
      StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have lengthBound : E.length < 2 ^ 32 := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  refine WP.seq (WP.mono (clear_ok v I) fun a ⟨Ia, zeros, F, K⟩ => ?_)
  refine WP.seq (wp_movS (readSrc_sc Ia.scratch (d := 32) (by omega)) fun b B _ =>
    WP.mono (cmp_src_cf (readSrc_sc (Ia.scratch.of_keeps B.keeps (by decide)) (d := 4) (by omega)))
      fun d ⟨C, carry⟩ => ?_)
  have M : d.mem = a.mem := C.mem.trans B.mem
  have Ka : Keeps [.eax] a d := B.keeps.widen (C.keeps [])
  have Id := Ia.keepMem v M Ka (by decide) (by decide) (C.syms.trans B.syms)
  have zd : Spec.Rsa.bytesAt d.mem (E.out.setWidth 64) E.length = List.replicate E.length 0 := by rw [M]; exact zeros
  have Fd : MutableFrame E s.mem d.mem := by rw [M]; exact F
  have Kd : Keeps WitnessStep.clob s d := (K.mono (by unfold WitnessStep.clob; decide)).trans (Ka.mono (by unfold WitnessStep.clob; decide))
  have condition : isa.eval .b d = some (decide (E.randLength < E.length)) := by
    change d.cf = _
    rw [carry, B.gpr, B.mem, Ia.header 8 (by decide), Ia.header 1 (by decide)]
    change some (decide ((BitVec.ofNat 32 E.randLength).toNat < (BitVec.ofNat 32 E.length).toNat)) = _
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.randLengthFit, Nat.mod_eq_of_lt lengthBound]
  by_cases enough : E.length ≤ E.randLength
  · refine WP.ite false (by rw [condition, decide_eq_false (by omega)]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (available_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Id zd enough)
      fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨(candidate_outputs_eq v eBytes pBytes entropy (by rw [Id.memory.entropyLength]; exact enough) t).mp output,
      Fd.trans Ft, Kd.trans Kt⟩
  · refine WP.ite true (by rw [condition, decide_eq_true (by omega)]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (no_entropy_ok v Id zd) fun t ⟨output, Ft, Kt⟩ => ?_
    have exhausted : ¬ E.length ≤ entropy.length := by rw [Id.memory.entropyLength]; exact enough
    have spec : Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy = none := by
      unfold Spec.RsaKeyGen.candidateOp
      rw [VG.Proof.RsaKeyGen.candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega),
        VG.Proof.RsaKeyGen.ite_f exhausted]
    exact ⟨by rw [spec]; exact output, Fd.trans Ft, Kd.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

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
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
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
