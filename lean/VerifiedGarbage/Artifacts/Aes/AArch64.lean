module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Frame
public import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.Scratch
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Spec

/-! # AES on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Aes.AArch64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The working space is in a frame of 512 \
        bytes on the stack, zeroed before returning."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.Aes.AArch64.expandKey
    stack := 512
    verified := Proof.Aes.AArch64.expandKey_framed Proof.Aes.AArch64.expandKey_verified },
  Spec.Aes.expandKeyScratchApi.artifact AArch64.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.AArch64.expandKey
    verified := Proof.Aes.AArch64.expandKey_verified },
  Spec.Gcm.ctr32Api.artifact AArch64.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.AArch64.ctr32
    verified := Proof.Aes.AArch64.ctr32_verified },
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses the Armv8 Cryptographic Extension: one word at a time, with AESE for \
        `SUBWORD`. The working space is in a frame of 512 bytes on the stack, zeroed before \
        returning."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64
      Impl.Aes.AArch64.Aese.expandKey
    stack := 512
    verified := Proof.Aes.AArch64.expandKey_framed Proof.Aes.AArch64.Aese.Key.expandKey_verified
    features := ["aes"] },
  Spec.Aes.expandKeyScratchApi.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses the Armv8 Cryptographic Extension: one word at a time, with AESE for \
        `SUBWORD`."]
    code := Impl.Aes.AArch64.Aese.expandKey
    verified := Proof.Aes.AArch64.Aese.Key.expandKey_verified
    features := ["aes"] },
  Spec.Gcm.ctr32Api.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses the Armv8 Cryptographic Extension (AESE, AESMC). The round keys stay in \
        registers; eight blocks at a time, then one at a time."]
    code := Impl.Aes.AArch64.Aese.ctr32
    verified := Proof.Aes.AArch64.Aese.ctr32_verified
    features := ["aes"] },
  Spec.Aes.encryptBlocksApi.artifact AArch64.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.AArch64.encryptBlocks
    verified := Proof.Aes.AArch64.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact AArch64.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."]
    code := Impl.Aes.AArch64.decryptBlocks
    verified := Proof.Aes.AArch64.decryptBlocks_verified },
  Spec.Aes.encryptBlocksApi.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses the Armv8 Cryptographic Extension (AESE, AESMC). The round keys stay in \
        registers; eight blocks at a time, then one at a time. `scratch` is not used."]
    written := [("scratch", 0)]
    code := Impl.Aes.AArch64.Aese.encryptBlocks
    verified := Proof.Aes.AArch64.Aese.encryptBlocks_verified
    writtenOk := Proof.Aes.AArch64.Aese.encryptBlocks_written
    features := ["aes"] },
  Spec.Aes.decryptBlocksApi.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses the Armv8 Cryptographic Extension (AESD, AESIMC): the equivalent inverse \
        cipher (FIPS 197 §5.3.5), with the round keys of the middle rounds through AESIMC, kept \
        in registers; eight blocks at a time, then one at a time. `scratch` is not used."]
    written := [("scratch", 0)]
    code := Impl.Aes.AArch64.Aese.decryptBlocks
    verified := Proof.Aes.AArch64.Aese.decryptBlocks_verified
    writtenOk := Proof.Aes.AArch64.Aese.decryptBlocks_written
    features := ["aes"] }]

end VG.Artifacts.Aes.AArch64
