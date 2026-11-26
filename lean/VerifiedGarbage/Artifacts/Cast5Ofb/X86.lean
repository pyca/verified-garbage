module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Proof.Cast5.X86.Scrub
import VerifiedGarbage.Impl.Cast5.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
import VerifiedGarbage.Impl.Cast5.X86.Ssse3
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-OFB on x86 -/

namespace VG.Artifacts.Cast5Ofb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Cast5.ofbApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.ofb
    verified := Proof.Cast5.X86.Ssse3.ofb_scrubbed },
  Spec.Cast5.ofbApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.ofb
    verified := Proof.Cast5.X86.Scrub.ofb_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.ofbFinal
    verified := Proof.Cast5.X86.Ssse3.ofbFinal_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.ofbFinal
    verified := Proof.Cast5.X86.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Ofb.X86
