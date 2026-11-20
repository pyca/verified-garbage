module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit

/-! # Triple DES-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ofb, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ofb_spSafe },
  Spec.TripleDes.ofbFinalApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ofbFinal, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.TripleDesOfb.X86_64
