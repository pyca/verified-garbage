module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-CBC decryption with thirty-two AVX-512 VAES states -/

@[expose] public section
namespace VG.Artifacts.AesCbc.X86_64

def artifacts : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.X86_64.target {
    suffix := "_vaes_avx512"
    code := Proof.AesCbc.X86_64.Wiped.decryptVaes512
    stack := 32
    spSafe := Proof.AesCbc.X86_64.Wiped.decryptVaes512_spSafe
    verified := Proof.AesCbc.X86_64.Wiped.decryptVaes512_verified
    features := ["aes","avx","avx2","vaes","avx512f"] }]

end VG.Artifacts.AesCbc.X86_64
