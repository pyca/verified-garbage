module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Aes.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Aes.PPC64LE

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact PPC64LE.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The working space is in a frame of 544 bytes \
        on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r6 64 Impl.Aes.PPC64LE.expandKey
    stack := 544
    verified := Proof.Aes.PPC64LE.expandKey_framed },
  Spec.Aes.expandKeyScratchApi.artifact PPC64LE.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.PPC64LE.expandKey
    verified := Proof.Aes.PPC64LE.expandKey_verified },
  Spec.Gcm.ctr32Api.artifact PPC64LE.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.PPC64LE.ctr32
    verified := Proof.Aes.PPC64LE.ctr32_verified },
  Spec.Aes.encryptBlocksApi.artifact PPC64LE.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.PPC64LE.encryptBlocks
    verified := Proof.Aes.PPC64LE.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact PPC64LE.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."]
    code := Impl.Aes.PPC64LE.decryptBlocks
    verified := Proof.Aes.PPC64LE.decryptBlocks_verified }]

end VG.Artifacts.Aes.PPC64LE
