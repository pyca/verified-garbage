module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
import VerifiedGarbage.Impl.Camellia.X86_64.Fn
import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-OFB on x86-64 -/

namespace VG.Artifacts.CamelliaOfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Camellia.ofbApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ofb, verified := Proof.Camellia.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ofb_spSafe },
  Spec.Camellia.ofbFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ofbFinal, verified := Proof.Camellia.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.CamelliaOfb.X86_64
