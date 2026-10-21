module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Preserve
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64CheckTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSaveTiming

/-! # Candidate restoration keeps the general exponent check independent of secret values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.RsaKeyGen.X86.Gcd64

theorem preserving_trace (n dst saved offset : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (preserving n dst saved offset)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (setup_trace offset) (RelCT.seq code_trace
    (RelCT.seq (CandidateSave.restore_workspace_trace n saved dst) result_trace))

end VG.Proof.RsaKeyGen.X86.Gcd64
