module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES (FIPS 197) on PPC64LE -/

namespace VG.Artifacts.Aes.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Aes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.expandKey
    verified := Proof.Aes.PPC64LE.Scrub.expandKey_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Aes.PPC64LE
