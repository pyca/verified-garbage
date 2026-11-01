module

public import VerifiedGarbage.Proof.Md5.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Md5.X86_64.Lit

/-! # MD5 (RFC 1321) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact X86_64.target {
    code := Impl.Md5.X86_64.Stream.init
    verified := Proof.Md5.X86_64.Shared.init },
  Spec.Md5.updateApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 120 .r8 Impl.Md5.X86_64.Stream.update
    stack := 8 + 120
    verified := Proof.Md5.X86_64.Shared.update },
  Spec.Md5.finalizeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 120 .rcx Impl.Md5.X86_64.Stream.finalize
    stack := 8 + 120
    verified := Proof.Md5.X86_64.Shared.finalize }]

end VG.Artifacts.Md5.X86_64
