module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.X86.Scrub
import VerifiedGarbage.Impl.Md5.X86.Stream
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # MD5 (RFC 1321) on x86 -/

namespace VG.Artifacts.Md5.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Md5.initApi.artifact X86.target {
    code := Impl.Md5.X86.Fn.init
    verified := Proof.Md5.X86.Scrub.init_scrubbed },
  Spec.Md5.updateApi.artifact X86.target {
    code := Impl.Md5.X86.Fn.update
    verified := Proof.Md5.X86.Scrub.update_scrubbed },
  Spec.Md5.finalizeApi.artifact X86.target {
    code := Impl.Md5.X86.Fn.finalize
    verified := Proof.Md5.X86.Scrub.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Md5.X86
