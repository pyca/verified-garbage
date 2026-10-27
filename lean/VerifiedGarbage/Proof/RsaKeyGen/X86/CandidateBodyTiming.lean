module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBody
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEntryTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpCode
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters

/-! # Native argument entry and the complete candidate body obey the declared leak -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure BodyPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : EntryInput E eBytes pBytes rBytes s
  right : EntryInput E eBytes qBytes sBytes t

theorem enter_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.CandidateArgs.enter
      (InputPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have trace := (CandidateArgs.enter_trace _ _ _ _ _ _ ⟨P.left.arguments, P.right.arguments⟩ A B).1
  obtain ⟨IU, _, _⟩ := wp_result (enter_input_ok v P.left) A
  obtain ⟨IZ, _, _⟩ := wp_result (enter_input_ok v P.right) B
  exact ⟨trace, IU, IZ⟩

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (fun _ _ => True) :=
    RelCT.seq (enter_pair_trace v) (front_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      P.left.memory.entropyLength P.right.memory.entropyLength leak)
  refine ⟨(raw _ _ _ _ _ _ P A B).1, agree_regs ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [Exec.gpr (CandidateNoSp.body montNoSp roundNoSp montName roundName) A,
    Exec.gpr (CandidateNoSp.body montNoSp roundNoSp montName roundName) B]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.Candidate
