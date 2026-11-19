module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit

/-! # Triple DES-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86.target Proof.TripleDes.X86.Scrub.ofbReg,
  Spec.TripleDes.ofbFinalApi.artifact X86.target Proof.TripleDes.X86.Scrub.ofbFinalReg]

end VG.Artifacts.TripleDesOfb.X86
