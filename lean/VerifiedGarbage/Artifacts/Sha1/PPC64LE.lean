module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-1 (FIPS 180-4) on PPC64LE -/

namespace VG.Artifacts.Sha1.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sha1.initApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Stream.init
    verified := Proof.Sha1.PPC64LE.init_scrubbed },
  Spec.Sha1.updateApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.update
    verified := Proof.Sha1.PPC64LE.update_scrubbed },
  Spec.Sha1.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.finalize
    verified := Proof.Sha1.PPC64LE.finalize_scrubbed },
  Spec.Sha1.digestApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.digest
    verified := Proof.Sha1.PPC64LE.digest_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sha1.PPC64LE
