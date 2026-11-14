module

public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.cbcEncryptChainedReg,
  Spec.Cast5.cbcDecryptChainedApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Cast5Cbc.X86_64
