module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit
public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-CBC (NIST SP 800-38A §6.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.AArch64

def direct : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes_sha3"
    code := Impl.AesCbc.AArch64.Decrypt.code
    verified := Proof.AesCbc.AArch64.Wiped.decryptSha3_scrubbed
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.written },
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Decrypt.codeAes
    verified := Proof.AesCbc.AArch64.Wiped.decryptAes_scrubbed
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenAes }]

end VG.Artifacts.AesCbc.AArch64

namespace VG.Artifacts.AesCbc.AArch64

open VG.Proof.AesCbc.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) =>
    (Wiped.encryptRegs v).map (Spec.Cbc.aesEncryptApi.artifact AArch64.target) ++
      (Wiped.decryptRegs v).map (Spec.Cbc.aesDecryptApi.artifact AArch64.target))

end VG.Artifacts.AesCbc.AArch64
