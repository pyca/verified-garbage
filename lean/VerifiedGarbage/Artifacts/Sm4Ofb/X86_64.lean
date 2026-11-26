module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Impl.Sm4.X86_64.Fn
import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-OFB on x86-64 -/

namespace VG.Artifacts.Sm4Ofb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sm4.ofbApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ofb, verified := Proof.Sm4.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ofb_spSafe },
  Spec.Sm4.ofbFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ofbFinal, verified := Proof.Sm4.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sm4Ofb.X86_64
