module

public import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
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
    verified := Proof.Camellia.AArch64.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.AArch64
