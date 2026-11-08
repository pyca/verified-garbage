module

public import VerifiedGarbage.Proof.AesXts.X86.Verified
public import VerifiedGarbage.Proof.AesXts.X86.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86

open VG.Proof.AesXts.X86

def artifactsFor (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesXts.X86Unit.encrypt (Unit.xtsE v)
    stack := 52
    verified := Unit.encrypt_verified v
    spSafe := Unit.encrypt_spSafe v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesXts.X86Unit.decrypt (Unit.xtsE v) (Unit.xtsD v)
    stack := 52
    verified := Unit.decrypt_verified v
    spSafe := Unit.decrypt_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesXts.X86
