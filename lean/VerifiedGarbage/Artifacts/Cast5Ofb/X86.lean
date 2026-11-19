module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit

/-! # CAST5-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.X86

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact X86.target Proof.Cast5.X86.Scrub.ofbReg,
  Spec.Cast5.ofbFinalApi.artifact X86.target Proof.Cast5.X86.Scrub.ofbFinalReg]

end VG.Artifacts.Cast5Ofb.X86
