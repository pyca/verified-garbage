module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Impl.Cast5.X86_64.Fn
import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-OFB on x86-64 -/

namespace VG.Artifacts.Cast5Ofb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Cast5.ofbApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ofb, verified := Proof.Cast5.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ofb_spSafe },
  Spec.Cast5.ofbFinalApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ofbFinal, verified := Proof.Cast5.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.Cast5Ofb.X86_64
