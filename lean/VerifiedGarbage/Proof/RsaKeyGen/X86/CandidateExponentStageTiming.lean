module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFilterTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInput
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming

/-! # Publicly released coprimality decisions select equally timed candidate continuations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

theorem drawn_used_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} (status : Nat) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (fun _ _ => True) := by
  exact (CandidateFinish.used_trace (base := E.base) (size := E.size)
    (by have H : 256 ≤ E.size := v.geometry.headerFit; omega) status).mono (fun _ _ P =>
      ⟨P.left.input.scratch, P.right.input.scratch, P.left.input.usedPointer.trans P.right.input.usedPointer.symm⟩) (fun _ _ _ => trivial)

theorem exponent_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateExponent.code E.width)
      (WithFlag (TestPair E eBytes pBytes qBytes rBytes sBytes)
        (decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1))) := by
  intro s t tr ur u z P A B
  have trace := (exponent_trace v _ _ _ _ _ _ P A B).1
  obtain ⟨DU, flagU, saveU, _, _⟩ := wp_result (exponent_ok v P.left) A
  obtain ⟨DZ, flagZ, saveZ, _, _⟩ := wp_result (exponent_ok v P.right) B
  exact ⟨trace, ⟨⟨DU, DZ⟩, saveU, saveZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem exponent_stage_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (same : decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1))
    (shape : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1 →
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
        shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck E.width montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck
  by_cases good : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1
  · have initialTrace := exponent_pair_trace (pBytes := pBytes) (qBytes := qBytes) v same
    rw [decide_eq_true good] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.1)) ?_)
    exact branch_false (prepared_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough (shape good))
  · have initialTrace := exponent_pair_trace (pBytes := pBytes) (qBytes := qBytes) v same
    rw [decide_eq_false good] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.1)) ?_)
    exact branch_true ((drawn_used_trace v 3).mono (fun _ _ P => P.toDrawnPair) (fun _ _ _ => trivial))

end VG.Proof.RsaKeyGen.X86.Candidate
