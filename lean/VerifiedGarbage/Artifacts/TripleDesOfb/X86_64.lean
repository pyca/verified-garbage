module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit

/-! # Triple DES-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ofbReg,
  Spec.TripleDes.ofbFinalApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ofbFinalReg]

end VG.Artifacts.TripleDesOfb.X86_64
