module

public import VerifiedGarbage.Proof.Md5.AArch64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # MD5 (RFC 1321) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Md5.AArch64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.init
    verified := Proof.Md5.AArch64.Shared.init },
  Spec.Md5.updateApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Md5.AArch64.Stream.update
    stack := 16 + 112
    verified := Proof.Md5.AArch64.Shared.update },
  Spec.Md5.finalizeApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 Impl.Md5.AArch64.Stream.finalize
    stack := 16 + 112
    verified := Proof.Md5.AArch64.Shared.finalize }]

end VG.Artifacts.Md5.AArch64
