module

public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit

/-! # Camellia-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.ofbReg,
  Spec.Camellia.ofbFinalApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.ofbFinalReg]

end VG.Artifacts.CamelliaOfb.X86_64
