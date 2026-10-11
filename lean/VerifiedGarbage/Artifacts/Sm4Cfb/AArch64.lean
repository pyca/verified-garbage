import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified

/-! # SM4-CFB128 artifacts on baseline AArch64 -/

namespace VG.Artifacts.Sm4Cfb.AArch64

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
  lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is \
  built once per call. The mode is the generic CFB of `Impl/Modes/AArch64/`, over SM4's ECB core, with the IV's \
  address kept in a vector register across the core's code."

def artifacts : List Artifact := [
  { Spec.Sm4.cfbEncryptApi with
    target := AArch64.target
    doc := Spec.Sm4.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.cfbEncrypt
    contract := Spec.Sm4.cfbEncryptContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.cfbDecryptApi with
    target := AArch64.target
    doc := Spec.Sm4.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.cfbDecrypt
    contract := Spec.Sm4.cfbDecryptContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Cfb.AArch64
