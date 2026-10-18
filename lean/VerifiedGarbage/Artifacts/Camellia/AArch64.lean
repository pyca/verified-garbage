module

public import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Camellia.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 64-bit words."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x3 406 Impl.Camellia.AArch64.expandKey
    stack := 3248
    verified := Proof.Camellia.AArch64.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact AArch64.target {
    notes := ["Bitsliced on baseline AArch64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406
      (Impl.Camellia.AArch64.ecb .encrypt)
    stack := 3248
    verified := Proof.Camellia.AArch64.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact AArch64.target {
    notes := ["Bitsliced on baseline AArch64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406
      (Impl.Camellia.AArch64.ecb .decrypt)
    stack := 3248
    verified := Proof.Camellia.AArch64.ecb_framed .decrypt },
  (Spec.Camellia.Prepared.prepareApi Impl.Camellia.AArch64.layout).artifact AArch64.target {
    notes := ["Baseline AArch64: ECB's key setup alone, for the modes: the masks of the layers and the subkeys of 18 or 24 rounds bitsliced into the table of the working space, in the order `decrypt` selects, as eight copies each."]
    code := Impl.Camellia.AArch64.prepareKeys
    verified := Proof.Camellia.AArch64.prepare_verified },
  (Spec.Camellia.Prepared.cryptApi Impl.Camellia.AArch64.layout).artifact AArch64.target {
    notes := ["Baseline AArch64: ECB's eight blocks alone, for the modes: bitsliced in general-purpose registers, each half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table lookups, under the table `vg_camellia_prepare_keys` wrote."]
    code := Impl.Camellia.AArch64.cryptPrepared
    verified := Proof.Camellia.AArch64.crypt_verified }]

end VG.Artifacts.Camellia.AArch64
