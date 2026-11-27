module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesXts.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on PPC64LE -/

namespace VG.Artifacts.AesXts.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Xts.aesEncryptUnitApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LE.Fn.encryptUnit
    verified := Proof.AesXts.PPC64LE.Scrub.encryptUnit_scrubbed },
  Spec.Xts.aesDecryptUnitApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LE.Fn.decryptUnit
    verified := Proof.AesXts.PPC64LE.Scrub.decryptUnit_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesXts.PPC64LE
