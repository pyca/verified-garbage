module

public import VerifiedGarbage.Proof.Md5.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Md5.X86.Lit

/-! # MD5 (RFC 1321) on x86 -/

@[expose] public section

namespace VG.Artifacts.Md5.X86

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact X86.target {
    code := Impl.Md5.X86.Stream.init
    verified := Proof.Md5.X86.Shared.init },
  Spec.Md5.updateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 140 5 Impl.Md5.X86.Stream.update
    stack := 20 + 140
    verified := Proof.Md5.X86.Shared.update },
  Spec.Md5.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 136 4 Impl.Md5.X86.Stream.finalize
    stack := 20 + 136
    verified := Proof.Md5.X86.Shared.finalize }]

end VG.Artifacts.Md5.X86
