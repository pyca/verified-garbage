module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFilterTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCloseInput
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming

/-! # A candidate width hides distance-filtered and accepted prime values through its full path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

structure ClearedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends InputPair E eBytes pBytes qBytes rBytes sBytes s t where
  zerosLeft : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0
  zerosRight : Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem load_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (enough : E.length ≤ E.randLength) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) (VG.Impl.RsaKeyGen.X86.CandidateLoad.code E.width)
      (DrawnPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have trace := (load_trace v _ _ _ _ _ _ P.toInputPair A B).1
  obtain ⟨DU, _, _⟩ := wp_result (load_ok v P.left P.zerosLeft enough) A
  obtain ⟨DZ, _, _⟩ := wp_result (load_ok v P.right P.zerosRight enough) B
  exact ⟨trace, DU, DZ⟩

theorem close_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) (VG.Impl.RsaKeyGen.X86.CandidateClose.code E.width)
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes))) := by
  intro s t tr ur u z P A B
  have trace := (close_trace v _ _ _ _ _ _ P A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (close_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (close_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem close_stage_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq (VG.Impl.RsaKeyGen.X86.Candidate.closeCheck E.width)
        (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 2)
          (VG.Impl.RsaKeyGen.X86.Candidate.sieveCheck E.width montName mont roundName round)))) (fun _ _ => True) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) := by
    have H := congrArg Sched.close schedules
    rw [schedule_close, schedule_close] at H
    exact H
  have initialTrace := close_pair_trace (eBytes := eBytes) v same
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes)
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_false (sieve_stage_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length rEnough enough
      leak close (same.symm.trans close))
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_used_trace v 2)

theorem sized_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.sized E.width montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.sized VG.Impl.RsaKeyGen.X86.Candidate.importCandidate
  exact RelCT.seq (load_pair_trace v enough)
    (close_stage_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length rEnough enough leak)

end VG.Proof.RsaKeyGen.X86.Candidate
