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
    code := Proof.AesCbc.AArch64.Decrypt.codeC
    verified := .scrubbed ⟨Proof.AesCbc.AArch64.Wiped.decryptSha3C_scrubbed,
      Proof.AesCbc.AArch64.Decrypt.codeC_noResidue _⟩
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenC },
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Proof.AesCbc.AArch64.Decrypt.codeAesC
    verified := .scrubbed ⟨Proof.AesCbc.AArch64.Wiped.decryptAesC_scrubbed,
      Proof.AesCbc.AArch64.Decrypt.codeAesC_noResidue _⟩
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenAesC }]

end VG.Artifacts.AesCbc.AArch64

namespace VG.Artifacts.AesCbc.AArch64

open VG.Proof.AesCbc.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) =>
    (Wiped.encryptRegs v).map (Spec.Cbc.aesEncryptApi.artifact AArch64.target) ++
      (Wiped.decryptRegs v).map (Spec.Cbc.aesDecryptApi.artifact AArch64.target))

end VG.Artifacts.AesCbc.AArch64
