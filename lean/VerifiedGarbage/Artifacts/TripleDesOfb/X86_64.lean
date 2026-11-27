module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-OFB on x86-64 -/

namespace VG.Artifacts.TripleDesOfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.TripleDes.ofbApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ofb, verified := Proof.TripleDes.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ofb_spSafe },
  Spec.TripleDes.ofbFinalApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ofbFinal, verified := Proof.TripleDes.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.TripleDesOfb.X86_64
