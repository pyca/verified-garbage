module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit

/-! # AES-CBC decryption with seven independent AES states -/

@[expose] public section

namespace VG.Artifacts.AesCbc.AArch64

def artifacts : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes_sha3"
    code := Impl.AesCbc.AArch64.Decrypt.code
    verified := Proof.AesCbc.AArch64.Wiped.decryptSha3_scrubbed
    features := ["aes","sha3"]
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.written },
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Decrypt.codeAes
    verified := Proof.AesCbc.AArch64.Wiped.decryptAes_scrubbed
    features := ["aes"]
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenAes }]

end VG.Artifacts.AesCbc.AArch64
