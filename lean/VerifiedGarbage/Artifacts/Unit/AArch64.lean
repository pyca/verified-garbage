module

public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesXts.AArch64

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole data units on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Unit.AArch64

open VG.Proof.AesXts.AArch64.Unit

def artifactsFor (v : Proof.AesXts.AArch64.XtsImpl) : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesXts.AArch64Unit.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesXts.AArch64Unit.decrypt v.enc v.dec
    verified := decrypt_verified v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesXts.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Unit.AArch64
