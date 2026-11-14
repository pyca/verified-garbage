module

public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.cbcEncryptReg,
  Spec.Sm4.cbcDecryptChainedApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.cbcDecryptReg]

end VG.Artifacts.Sm4Cbc.X86_64
