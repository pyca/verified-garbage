module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit

/-! # CAST5-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.Cast5Ofb.X86
