module

public import VerifiedGarbage.Proof.Md5.AArch64.Shared
public import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # MD5 (RFC 1321) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Md5.AArch64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.init
    verified := .scrubbed Proof.Md5.AArch64.Stream.init_scrubbed },
  Spec.Md5.updateApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.Fn.update
    verified := .scrubbed Proof.Md5.AArch64.Shared.update_scrubbed },
  Spec.Md5.finalizeApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.Fn.finalize
    verified := .scrubbed Proof.Md5.AArch64.Shared.finalize_scrubbed }]

end VG.Artifacts.Md5.AArch64
