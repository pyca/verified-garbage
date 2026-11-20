module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.FbLit
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit

/-! # SM4-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.X86

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ofb
    verified := .scrubbed Proof.Sm4.X86.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ofbFinal
    verified := .scrubbed Proof.Sm4.X86.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.Sm4Ofb.X86
