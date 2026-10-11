import VerifiedGarbage.Proof.Sm4.X86.CbcVerified

/-! # SM4-CBC artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.Sm4Cbc.X86

def artifacts : List Artifact := [
  { Spec.Sm4.cbcEncryptApi with
    target := X86.target
    doc := Spec.Sm4.cbcEncryptApi.doc
      (notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the key schedule's table of round keys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/X86/`, over SM4's ECB core."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 Impl.Sm4.X86.cbcEncrypt
    contract := Spec.Sm4.cbcEncryptContract X86.abi 1472
    stack := 1472
    verified := Proof.Sm4.X86.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm4.cbcDecryptApi with
    target := X86.target
    doc := Spec.Sm4.cbcDecryptApi.doc
      (notes := ["Baseline IA-32: one block at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the key schedule's table of round keys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/X86/`, over SM4's ECB core."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 Impl.Sm4.X86.cbcDecrypt
    contract := Spec.Sm4.cbcDecryptContract X86.abi 1472
    stack := 1472
    verified := Proof.Sm4.X86.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sm4Cbc.X86
