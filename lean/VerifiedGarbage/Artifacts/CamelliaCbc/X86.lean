module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.CbcLit

/-! # Camellia-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target Proof.Camellia.X86.Scrub.cbcEncryptChainedReg,
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target Proof.Camellia.X86.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.CamelliaCbc.X86
