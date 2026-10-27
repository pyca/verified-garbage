module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.TCB.X86.Isa

/-! # Live candidate inputs satisfy the timing preconditions of every prefilter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem exponent_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code (fun _ _ => True) :=
  CandidateExponent.code_trace.mono (fun _ _ P => ⟨P.left.exponentInitial v, P.right.exponentInitial v⟩) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.Candidate
