module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.FbLit
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit

/-! # Camellia-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact X86.target Proof.Camellia.X86.Scrub.ofbReg,
  Spec.Camellia.ofbFinalApi.artifact X86.target Proof.Camellia.X86.Scrub.ofbFinalReg]

end VG.Artifacts.CamelliaOfb.X86
