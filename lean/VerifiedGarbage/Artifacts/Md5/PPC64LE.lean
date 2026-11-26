module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # MD5 (RFC 1321) on PPC64LE -/

namespace VG.Artifacts.Md5.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Md5.initApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Stream.init
    verified := Proof.Md5.PPC64LE.init_scrubbed },
  Spec.Md5.updateApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Fn.update
    verified := Proof.Md5.PPC64LE.update_scrubbed },
  Spec.Md5.finalizeApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Fn.finalize
    verified := Proof.Md5.PPC64LE.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Md5.PPC64LE
