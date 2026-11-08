module

public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Verified
public import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesXts.X86_64

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole data units on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Unit.X86_64

open VG.Proof.AesXts.X86_64.Unit

def artifactsFor (v : Proof.AesXts.X86_64.XtsImpl) : List Artifact := [
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
    features := v.features },
  Spec.Xts.aesEncryptUnitToApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesXts.X86_64UnitTo.encrypt v.xts (Proof.AesXts.X86_64.UnitTo.UnitImpl.of v).xt
    stack := 24
    verified := Proof.AesXts.X86_64.UnitTo.encrypt_verified (.of v)
    spSafe := Proof.AesXts.X86_64.UnitTo.encrypt_spSafe (.of v)
    features := v.features },
  Spec.Xts.aesDecryptUnitToApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesXts.X86_64UnitTo.decrypt v.xts (Proof.AesXts.X86_64.UnitTo.UnitImpl.of v).xt
    stack := 24
    verified := Proof.AesXts.X86_64.UnitTo.decrypt_verified (.of v)
    spSafe := Proof.AesXts.X86_64.UnitTo.decrypt_spSafe (.of v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesXts.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Unit.X86_64
