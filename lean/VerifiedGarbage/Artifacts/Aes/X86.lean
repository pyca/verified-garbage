import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
import VerifiedGarbage.Proof.Aes.X86.BlocksCT
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
import VerifiedGarbage.Proof.Aes.X86.Frame

/-! # AES on x86 -/

namespace VG.Artifacts.Aes.X86

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := X86.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence). The working space is in a frame of 532 bytes \
        on the stack, zeroed before returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
    contract := Spec.Aes.expandKeyContract X86.abi 532
    stack := 532
    verified := Proof.Aes.X86.scalar_expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyScratchApi with
    target := X86.target
    doc := Spec.Aes.expandKeyScratchApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86.expandKey
    contract := Spec.Aes.expandKeyScratchContract X86.abi
    verified := Proof.Aes.X86.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    target := X86.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86.ctr32
    contract := Spec.Gcm.ctr32Contract X86.abi
    verified := Proof.Aes.X86.ctr32_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_aesni"
    target := X86.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["AES-NI, six blocks at a time followed by a one-block tail. The low counter \
        word increments modulo 2^32; the first twelve counter bytes stay fixed."])
    code := Impl.Aes.X86.AesNi.ctr32
    contract := Spec.Gcm.ctr32Contract X86.abi
    verified := Proof.Aes.X86.AesNi.ctr32_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyApi with
    name := "vg_aes_expand_key_aesni"
    target := X86.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["AES-NI key expansion with `AESKEYGENASSIST` for AES-128, AES-192 and AES-256. \
        Its working space, unused, is in a frame of 532 bytes on the stack, zeroed before \
        returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey
    contract := Spec.Aes.expandKeyContract X86.abi 532
    stack := 532
    verified := Proof.Aes.X86.aesni_expandKey_framed
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyScratchApi with
    name := "vg_aes_expand_key_scratch_aesni"
    target := X86.target
    doc := Spec.Aes.expandKeyScratchApi.doc
      (notes := ["AES-NI key expansion with `AESKEYGENASSIST` for AES-128, AES-192 and AES-256. \
        The scratch buffer is unused."])
    code := Impl.Aes.X86.AesNi.expandKey
    contract := Spec.Aes.expandKeyScratchContract X86.abi
    verified := Proof.Aes.X86.AesNi.expandKey_verified
      ⟨Proof.Aes.X86.AesNi.expand128_ok, Proof.Aes.X86.AesNi.expand192_ok,
        Proof.Aes.X86.AesNi.expand256_ok⟩
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.encryptBlocksApi with
    target := X86.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract X86.abi
    verified := Proof.Aes.X86.encryptBlocks_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Aes.decryptBlocksApi with
    target := X86.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."])
    code := Impl.Aes.X86.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract X86.abi
    verified := Proof.Aes.X86.decryptBlocks_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Aes.encryptBlocksApi with
    name := "vg_aes_encrypt_blocks_aesni"
    target := X86.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Uses AES-NI: six blocks at a time, then one at a time."])
    code := Impl.Aes.X86.AesNi.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract X86.abi
    verified := Proof.Aes.X86.AesNi.encryptBlocks_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Aes.decryptBlocksApi with
    name := "vg_aes_decrypt_blocks_aesni"
    target := X86.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Uses AES-NI: the equivalent inverse cipher (FIPS 197 §5.3.5), with the round keys \
        through `AESIMC` in the scratch buffer; six blocks at a time, then one at a time."])
    code := Impl.Aes.X86.AesNi.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract X86.abi
    verified := Proof.Aes.X86.AesNi.decryptBlocks_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Aes.X86
