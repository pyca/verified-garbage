module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish on PPC64LE -/

namespace VG.Artifacts.Blowfish.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Blowfish.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.expandKey
    verified := Proof.Blowfish.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Blowfish.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Blowfish.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blowfish.PPC64LE
