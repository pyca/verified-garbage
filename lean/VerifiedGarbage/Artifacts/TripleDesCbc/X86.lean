module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.CbcLit

/-! # Triple DES-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86.target Proof.TripleDes.X86.Scrub.cbcEncryptChainedReg,
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86.target Proof.TripleDes.X86.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.TripleDesCbc.X86
