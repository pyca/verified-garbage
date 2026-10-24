module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultSpec
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateAvailable
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClearInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoEntropy
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters

/-! # Clearing, the public entropy guard, and width dispatch implement the candidate operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem front_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
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
