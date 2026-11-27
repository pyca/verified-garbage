module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5 (RFC 2144) on PPC64LE -/

namespace VG.Artifacts.Cast5.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cast5.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.expandKey
    verified := Proof.Cast5.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Cast5.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Cast5.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5.PPC64LE
