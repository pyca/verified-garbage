module

public import VerifiedGarbage.Impl.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.AesCbc.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.X86

open VG.Proof.AesCbc.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    if h : Proof.AesCbc.X86.Wiped.encWritten v = 0 then
      Spec.Cbc.aesEncryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Fn.free (Proof.AesCbc.X86.Wiped.encryptCode v)
        verified := .scrubbed (encryptFree_scrubbed v h)
        spSafe := encryptFree_fnSpSafe v }
    else
      Spec.Cbc.aesEncryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Fn.encrypt (Proof.AesCbc.X86.Wiped.encryptCode v) v.suffix (Proof.AesCbc.X86.Wiped.encWritten v)
        verified := .scrubbed (encryptWiped_scrubbed v h)
        spSafe := encryptWiped_fnSpSafe v },
    if h : Proof.AesCbc.X86.Wiped.decWritten v = 0 then
      Spec.Cbc.aesDecryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Fn.free (Proof.AesCbc.X86.Wiped.decryptCode v)
        verified := .scrubbed (decryptFree_scrubbed v h)
        spSafe := decryptFree_fnSpSafe v }
    else
      Spec.Cbc.aesDecryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Fn.decrypt (Proof.AesCbc.X86.Wiped.decryptCode v) v.suffix (Proof.AesCbc.X86.Wiped.decWritten v)
        verified := .scrubbed (decryptWiped_scrubbed v)
        spSafe := decryptWiped_fnSpSafe v }]

end VG.Artifacts.AesCbc.X86
