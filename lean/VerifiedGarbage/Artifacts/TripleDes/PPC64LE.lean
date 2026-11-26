module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Verified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES on PPC64LE -/

namespace VG.Artifacts.TripleDes.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.TripleDes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.expandKey
    verified := Proof.TripleDes.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.ecbEncrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.ecbDecrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDes.PPC64LE
