module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
public import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit

/-! # Triple DES-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.TripleDesOfb.X86
