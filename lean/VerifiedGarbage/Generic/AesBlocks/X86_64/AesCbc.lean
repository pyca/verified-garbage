module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Caller
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesCbc

open VG.Proof.AesCbc.X86_64

/-- Encryption, which is sequential, runs the same code with VAES as with
AES-NI (`Caller.encrypt`), so it has no VAES variant. -/
def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact :=
  (if Caller.vaes v then [] else [
  Spec.Cbc.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Caller.encrypt v
    stack := 8
    verified := Proof.AesCbc.encrypt_keyed (Caller.verified v)
    spSafe := Caller.spSafe v
    written := Caller.written v
    writtenOk := Caller.written_ok v
    features := Caller.encFeatures v }]) ++ [
  Spec.Cbc.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Caller.decrypt v
    stack := 8
    verified := Proof.AesCbc.decrypt_keyed (Caller.decryptVerified v)
    spSafe := Caller.decryptSpSafe v
    written := Caller.decWritten v
    writtenOk := Caller.decWritten_ok v
    features := Caller.decFeatures v }]

end VG.Generic.AesBlocks.X86_64.AesCbc
