module

public import VerifiedGarbage.Proof.AesEcb.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesEcb

open VG.Proof.AesEcb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.AesEcb.encryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesEcb.X86.wiped v.enc
    stack := 32
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.AesEcb.decryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesEcb.X86.wiped v.dec
    stack := 32
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesEcb
