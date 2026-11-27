module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Proof.Sm4.X86.Scrub
import VerifiedGarbage.Impl.Sm4.X86.Fn
import VerifiedGarbage.Proof.Sm4.X86.AesNiScrub
import VerifiedGarbage.Impl.Sm4.X86.AesNiFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.FbLit
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-OFB on x86 -/

namespace VG.Artifacts.Sm4Ofb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Sm4.ofbApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNi.Fn.ofb
    verified := Proof.Sm4.X86.AesNi.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ofb
    verified := Proof.Sm4.X86.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNi.Fn.ofbFinal
    verified := Proof.Sm4.X86.AesNi.Scrub.ofbFinal_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ofbFinal
    verified := Proof.Sm4.X86.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Ofb.X86
