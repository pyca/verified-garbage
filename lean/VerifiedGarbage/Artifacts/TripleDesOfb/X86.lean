module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Impl.TripleDes.X86.Fn
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-OFB on x86 -/

namespace VG.Artifacts.TripleDesOfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.TripleDes.ofbApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.ofb
    verified := Proof.TripleDes.X86.Ssse3.ofb_scrubbed },
  Spec.TripleDes.ofbApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.ofb
    verified := Proof.TripleDes.X86.Scrub.ofb_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.ofbFinal
    verified := Proof.TripleDes.X86.Ssse3.ofbFinal_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.ofbFinal
    verified := Proof.TripleDes.X86.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesOfb.X86
