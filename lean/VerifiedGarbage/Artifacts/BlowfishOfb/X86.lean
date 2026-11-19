module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit

/-! # Blowfish-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.X86

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact X86.target Proof.Blowfish.X86.Scrub.ofbReg,
  Spec.Blowfish.ofbFinalApi.artifact X86.target Proof.Blowfish.X86.Scrub.ofbFinalReg]

end VG.Artifacts.BlowfishOfb.X86
