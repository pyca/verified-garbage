module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit

/-! # CAST5 key expansion and ECB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact PPC64LE.target {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.PPC64LE.expandKey
    verified := Proof.Cast5.PPC64LE.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact PPC64LE.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.PPC64LE.ecbEncrypt
    verified := Proof.Cast5.PPC64LE.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact PPC64LE.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.PPC64LE.ecbDecrypt
    verified := Proof.Cast5.PPC64LE.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.PPC64LE
