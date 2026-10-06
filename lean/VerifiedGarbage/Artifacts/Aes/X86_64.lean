import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.Frame

/-! # AES on x86-64 -/

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := X86_64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The working space is in a frame of 520 \
        bytes on the stack, zeroed before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi 520
    stack := 520
    verified := Proof.Aes.X86_64.scalar_expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyScratchApi with
    target := X86_64.target
    doc := Spec.Aes.expandKeyScratchApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.expandKey
    contract := Spec.Aes.expandKeyScratchContract X86_64.abi
    verified := Proof.Aes.X86_64.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.ctr32_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyApi with
    name := "vg_aes_expand_key_aesni"
    target := X86_64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["Uses AES-NI: four words at a time, with AESKEYGENASSIST. The working space is \
        in a frame of 520 bytes on the stack, zeroed before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64
      Impl.Aes.X86_64.AesNi.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi 520
    stack := 520
    verified := Proof.Aes.X86_64.aesni_expandKey_framed
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyScratchApi with
    name := "vg_aes_expand_key_scratch_aesni"
    target := X86_64.target
    doc := Spec.Aes.expandKeyScratchApi.doc
      (notes := ["Uses AES-NI: four words at a time, with AESKEYGENASSIST."])
    code := Impl.Aes.X86_64.AesNi.expandKey
    contract := Spec.Aes.expandKeyScratchContract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.Key.expandKey_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_aesni"
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Uses AES-NI: eight blocks at a time, then one at a time."])
    code := Impl.Aes.X86_64.AesNi.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.ctr32_verified
    features := ["aes", "ssse3"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_vaes"
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Uses VAES: sixteen blocks at a time, two in each 256-bit register; the \
        blocks left go eight and then one at a time with AES-NI, as in `vg_aes_ctr32_aesni`."])
    code := Impl.Aes.X86_64.Vaes.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.Vaes.ctr32_verified
    features := ["aes", "avx", "avx2", "ssse3", "vaes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.encryptBlocksApi with
    target := X86_64.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract X86_64.abi
    verified := Proof.Aes.X86_64.encryptBlocks_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Aes.decryptBlocksApi with
    target := X86_64.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."])
    code := Impl.Aes.X86_64.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract X86_64.abi
    verified := Proof.Aes.X86_64.decryptBlocks_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Aes.encryptBlocksApi with
    name := "vg_aes_encrypt_blocks_aesni"
    target := X86_64.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Uses AES-NI: eight blocks at a time, then one at a time."])
    code := Impl.Aes.X86_64.AesNi.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.encryptBlocks_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Aes.decryptBlocksApi with
    name := "vg_aes_decrypt_blocks_aesni"
    target := X86_64.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Uses AES-NI: eight blocks at a time, then one at a time, with the Equivalent \
        Inverse Cipher (FIPS 197 §5.3.5): the middle round keys go through AESIMC into the \
        working space first."])
    code := Impl.Aes.X86_64.AesNi.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.decryptBlocks_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Aes.X86_64
