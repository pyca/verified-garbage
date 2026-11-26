module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CFB128 on PPC64LE -/

namespace VG.Artifacts.Sm4Cfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sm4.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Sm4.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Sm4.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Sm4.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Sm4.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cfb.PPC64LE
