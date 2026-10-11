import VerifiedGarbage.Proof.Sm4.X86_64.FbVerified

/-! # SM4-CFB128 artifacts on baseline x86-64 -/

namespace VG.Artifacts.Sm4Cfb.X86_64

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
  lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is \
  built once per call. The mode is the generic CFB of `Impl/Modes/X86_64/`, over SM4's ECB core."

def artifacts : List Artifact := [
  { Spec.Sm4.cfbEncryptApi with
    target := X86_64.target
    doc := Spec.Sm4.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 Impl.Sm4.X86_64.cfbEncrypt
    contract := Spec.Sm4.cfbEncryptContract X86_64.abi 3144
    stack := 3144
    verified := Proof.Sm4.X86_64.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sm4.cfbDecryptApi with
    target := X86_64.target
    doc := Spec.Sm4.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 Impl.Sm4.X86_64.cfbDecrypt
    contract := Spec.Sm4.cfbDecryptContract X86_64.abi 3144
    stack := 3144
    verified := Proof.Sm4.X86_64.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Sm4Cfb.X86_64
