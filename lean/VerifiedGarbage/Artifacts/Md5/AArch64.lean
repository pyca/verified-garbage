module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.AArch64.Shared
import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # MD5 (RFC 1321) on AArch64 -/

namespace VG.Artifacts.Md5.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Md5.initApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.init
    verified := Proof.Md5.AArch64.Stream.init_scrubbed },
  Spec.Md5.updateApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.Fn.update
    verified := Proof.Md5.AArch64.Shared.update_scrubbed },
  Spec.Md5.finalizeApi.artifact AArch64.target {
    code := Impl.Md5.AArch64.Stream.Fn.finalize
    verified := Proof.Md5.AArch64.Shared.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Md5.AArch64
