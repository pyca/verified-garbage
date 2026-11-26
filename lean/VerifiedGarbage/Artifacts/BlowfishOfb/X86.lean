module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Proof.Blowfish.X86.Scrub
import VerifiedGarbage.Impl.Blowfish.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-OFB on x86 -/

namespace VG.Artifacts.BlowfishOfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Blowfish.ofbApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Fn.ofb
    verified := Proof.Blowfish.X86.Ssse3.ofb_scrubbed },
  Spec.Blowfish.ofbApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ofb
    verified := Proof.Blowfish.X86.Scrub.ofb_scrubbed },
  Spec.Blowfish.ofbFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Fn.ofbFinal
    verified := Proof.Blowfish.X86.Ssse3.ofbFinal_scrubbed },
  Spec.Blowfish.ofbFinalApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ofbFinal
    verified := Proof.Blowfish.X86.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishOfb.X86
