module

public import VerifiedGarbage.Proof.AesXts.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesXts.PPC64LE

open VG.Proof.AesXts.PPC64LE

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LE.encrypt
    verified := encrypt_verified },
  Spec.Xts.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LE.decrypt
    verified := decrypt_verified },
  Spec.Xts.aesEncryptUnitApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LEUnit.encrypt
    verified := Unit.encrypt_verified },
  Spec.Xts.aesDecryptUnitApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LEUnit.decrypt
    verified := Unit.decrypt_verified }]

end VG.Artifacts.AesXts.PPC64LE
