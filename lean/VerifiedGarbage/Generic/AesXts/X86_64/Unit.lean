module

public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole data units on x86-64 -/

@[expose] public section

namespace VG.Generic.AesXts.X86_64.Unit

open VG.Proof.AesXts.X86_64.Unit

def artifacts (v : Proof.AesXts.X86_64.XtsImpl) : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesXts.X86_64Unit.encrypt v.xts
    stack := 16
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesXts.X86_64Unit.decrypt v.xts
    stack := 16
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesXts.X86_64.Unit
