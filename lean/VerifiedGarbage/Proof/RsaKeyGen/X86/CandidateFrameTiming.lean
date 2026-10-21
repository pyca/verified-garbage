module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBodyTiming
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Saving and restoring cdecl registers preserves candidate trace equivalence -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def FramedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  BodyPair E eBytes pBytes qBytes rBytes sBytes (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

theorem framed_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (FramedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) (fun _ _ => True) := by
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.RsaKeyGen.X86.Candidate.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v leak) restore).mono
    (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Candidate
