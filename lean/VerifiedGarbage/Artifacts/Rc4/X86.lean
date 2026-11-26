module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.X86.Scrub
import VerifiedGarbage.Impl.Rc4.X86
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.X86.Ssse3Verified
import VerifiedGarbage.Impl.Rc4.X86.Ssse3
import VerifiedGarbage.Proof.Rc4.X86.Lit
import VerifiedGarbage.Proof.Rc4.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC4 on x86 -/

namespace VG.Artifacts.Rc4.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Rc4.initApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Rc4.X86.Ssse3.Fn.init
    verified := Proof.Rc4.X86.Ssse3.init_scrubbed },
  Spec.Rc4.initApi.artifact X86.target {
    code := Impl.Rc4.X86.Fn.init
    verified := Proof.Rc4.X86.Scrub.init_scrubbed },
  Spec.Rc4.applyApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Rc4.X86.Ssse3.Fn.apply
    verified := Proof.Rc4.X86.Ssse3.apply_scrubbed },
  Spec.Rc4.applyApi.artifact X86.target {
    code := Impl.Rc4.X86.Fn.apply
    verified := Proof.Rc4.X86.Scrub.apply_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc4.X86
