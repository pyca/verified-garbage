import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Blocks
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks

/-! # AES on AArch64 -/

namespace VG.Artifacts.Aes.AArch64

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := AArch64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.expandKey
    contract := Spec.Aes.expandKeyContract AArch64.abi
    verified := Proof.Aes.AArch64.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.ctr32Api with
    target := AArch64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.ctr32
    contract := Spec.Gcm.ctr32Contract AArch64.abi
    verified := Proof.Aes.AArch64.ctr32_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.expandKeyApi with
    name := "vg_aes_expand_key_aes"
    target := AArch64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["Uses the Armv8 Cryptographic Extension: one word at a time, with AESE for \
        `SUBWORD`."])
    code := Impl.Aes.AArch64.Aese.expandKey
    contract := Spec.Aes.expandKeyContract AArch64.abi
    verified := Proof.Aes.AArch64.Aese.Key.expandKey_verified
    features := ["aes"]
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_aes"
    target := AArch64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Uses the Armv8 Cryptographic Extension (AESE, AESMC). The round keys stay in \
        registers; eight blocks at a time, then one at a time."])
    code := Impl.Aes.AArch64.Aese.ctr32
    contract := Spec.Gcm.ctr32Contract AArch64.abi
    verified := Proof.Aes.AArch64.Aese.ctr32_verified
    features := ["aes"]
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.encryptBlocksApi with
    target := AArch64.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract AArch64.abi
    verified := Proof.Aes.AArch64.encryptBlocks_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.decryptBlocksApi with
    target := AArch64.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."])
    code := Impl.Aes.AArch64.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract AArch64.abi
    verified := Proof.Aes.AArch64.decryptBlocks_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.encryptBlocksApi with
    name := "vg_aes_encrypt_blocks_aes"
    target := AArch64.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Uses the Armv8 Cryptographic Extension (AESE, AESMC). The round keys stay in \
        registers; eight blocks at a time, then one at a time. `scratch` is not used."])
    code := Impl.Aes.AArch64.Aese.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract AArch64.abi
    verified := Proof.Aes.AArch64.Aese.encryptBlocks_verified
    features := ["aes"]
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.decryptBlocksApi with
    name := "vg_aes_decrypt_blocks_aes"
    target := AArch64.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Uses the Armv8 Cryptographic Extension (AESD, AESIMC): the equivalent inverse \
        cipher (FIPS 197 §5.3.5), with the round keys of the middle rounds through AESIMC, kept \
        in registers; eight blocks at a time, then one at a time. `scratch` is not used."])
    code := Impl.Aes.AArch64.Aese.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract AArch64.abi
    verified := Proof.Aes.AArch64.Aese.decryptBlocks_verified
    features := ["aes"]
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Aes.AArch64
