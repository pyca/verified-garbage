module

public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.cbcEncryptReg,
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.cbcDecryptReg]

end VG.Artifacts.BlowfishCbc.X86_64
