module

public import VerifiedGarbage.Proof.Md5.X86.Scrub
public import VerifiedGarbage.Impl.Md5.X86.Stream
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Md5.X86.Lit

/-! # MD5 (RFC 1321) on x86 -/

@[expose] public section

namespace VG.Artifacts.Md5.X86

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact X86.target {
    code := Impl.Md5.X86.Fn.init
    verified := .scrubbed Proof.Md5.X86.Scrub.init_scrubbed },
  Spec.Md5.updateApi.artifact X86.target {
    code := Impl.Md5.X86.Fn.update
    verified := .scrubbed Proof.Md5.X86.Scrub.update_scrubbed },
  Spec.Md5.finalizeApi.artifact X86.target {
    code := Impl.Md5.X86.Fn.finalize
    verified := .scrubbed Proof.Md5.X86.Scrub.finalize_scrubbed }]

end VG.Artifacts.Md5.X86
