module

public import VerifiedGarbage.Proof.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCbc

open VG.Proof.AesCbc.X86.Wiped

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix
    stack := 72
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cbc.aesDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix
    stack := 72
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCbc
