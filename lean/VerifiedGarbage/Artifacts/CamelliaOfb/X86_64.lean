module

public import VerifiedGarbage.Impl.Camellia.X86_64.Fn
public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit

/-! # Camellia-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ofb, verified := Proof.Camellia.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ofb_spSafe },
  Spec.Camellia.ofbFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ofbFinal, verified := Proof.Camellia.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.CamelliaOfb.X86_64
