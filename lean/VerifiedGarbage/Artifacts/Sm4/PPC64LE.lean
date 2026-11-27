module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4 on PPC64LE -/

namespace VG.Artifacts.Sm4.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sm4.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.expandKey
    verified := Proof.Sm4.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Sm4.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Sm4.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4.PPC64LE
