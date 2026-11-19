module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit

/-! # Blowfish-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86.target Proof.Blowfish.X86.Scrub.cbcEncryptChainedReg,
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86.target Proof.Blowfish.X86.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.BlowfishCbc.X86
