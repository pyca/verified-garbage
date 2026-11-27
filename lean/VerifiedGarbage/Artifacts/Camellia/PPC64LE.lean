module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Camellia.PPC64LE.Verified
import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia on PPC64LE -/

namespace VG.Artifacts.Camellia.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Camellia.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.expandKey
    verified := Proof.Camellia.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ecbEnc
    verified := Proof.Camellia.PPC64LE.Scrub.ecbEnc_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ecbDec
    verified := Proof.Camellia.PPC64LE.Scrub.ecbDec_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Camellia.PPC64LE
