module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Wipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesCbc

open VG.Proof.AesCbc.X86_64

/-- Encryption, which is sequential, runs the same code with VAES as with
AES-NI (`Caller.encrypt`), so it has no VAES variant. Each implementation
that writes `scratch` zeroes what it writes before returning
(`Wipe.encrypt`, `Wipe.decrypt`); the loop in AES-NI registers writes none
of it. -/
def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact :=
  (if Caller.vaes v then [] else if Caller.hardware v then [
  Spec.Cbc.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Caller.encrypt v
    stack := 8
    verified := Proof.AesCbc.encrypt_keyed (Caller.verified v)
    spSafe := Caller.spSafe v
    written := Caller.written v
    writtenOk := Caller.written_ok v
    features := Caller.encFeatures v }] else [
  Spec.Cbc.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Wipe.encrypt v
    stack := 32
    verified := Wipe.encrypt_verified v
    spSafe := Wipe.encrypt_spSafe v
    features := Caller.encFeatures v }]) ++ [
  Spec.Cbc.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Wipe.decrypt v
    stack := 32
    verified := Wipe.decrypt_verified v
    spSafe := Wipe.decrypt_spSafe v
    features := Caller.decFeatures v }]

end VG.Generic.AesBlocks.X86_64.AesCbc
