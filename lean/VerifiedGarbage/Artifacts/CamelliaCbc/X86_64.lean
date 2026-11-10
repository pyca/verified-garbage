module

public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit

/-! # Camellia-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.cbcEncryptReg,
  Spec.Camellia.cbcDecryptChainedApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.cbcDecryptReg]

end VG.Artifacts.CamelliaCbc.X86_64
