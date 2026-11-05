module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Vaes512Decrypt
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-CBC decryption with thirty-two AVX-512 VAES states -/

@[expose] public section
namespace VG.Artifacts.AesCbc.X86_64

def artifacts : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.X86_64.target {
    suffix := "_vaes_avx512"
    code := Impl.AesCbc.X86_64.Vaes512Decrypt.decrypt
    stack := 8
    spSafe := Proof.AesCbc.X86_64.Vaes512Decrypt.spSafe
    verified := Proof.AesCbc.decrypt_keyed Proof.AesCbc.X86_64.Vaes512Decrypt.verified
    features := ["aes","avx","avx2","vaes","avx512f"]
    written := [("scratch",224)]
    writtenOk := Proof.AesCbc.X86_64.Vaes512Decrypt.written }]

end VG.Artifacts.AesCbc.X86_64
