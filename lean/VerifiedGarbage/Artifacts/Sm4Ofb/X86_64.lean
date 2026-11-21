module

public import VerifiedGarbage.Impl.Sm4.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit

/-! # SM4-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ofb, verified := .scrubbed Proof.Sm4.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ofb_spSafe },
  Spec.Sm4.ofbFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ofbFinal, verified := .scrubbed Proof.Sm4.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.Sm4Ofb.X86_64
