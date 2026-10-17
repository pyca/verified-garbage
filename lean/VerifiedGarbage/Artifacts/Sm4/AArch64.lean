module

public import VerifiedGarbage.Proof.Sm4.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: the key schedule's rounds bitsliced in general-purpose registers, sixteen copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x2 396 Impl.Sm4.AArch64.expandKey
    stack := 3168
    verified := Proof.Sm4.AArch64.expandKey_framed },
  Spec.Sm4.ecbDirApi.artifact AArch64.target {
    notes := ["Baseline AArch64: sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; `decrypt` selects the order in which the round keys are bitsliced into the working space, and the rounds are the same."]
    code := Proof.Sm4.AArch64.ecbAnyFramed
    stack := 3168
    verified := Proof.Sm4.AArch64.ecbAny_framed },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64: calls `vg_sm4_ecb` with `decrypt = 0`, saving the link register in a 16-byte stack frame."]
    code := Impl.Sm4.AArch64.ecbCall .encrypt Proof.Sm4.AArch64.ecbAnyFramed
    stack := 3184
    verified := Proof.Sm4.AArch64.ecbCall_verified .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64: calls `vg_sm4_ecb` with `decrypt = 1`, saving the link register in a 16-byte stack frame."]
    code := Impl.Sm4.AArch64.ecbCall .decrypt Proof.Sm4.AArch64.ecbAnyFramed
    stack := 3184
    verified := Proof.Sm4.AArch64.ecbCall_verified .decrypt },
  (Spec.Sm4.Prepared.prepareApi Impl.Sm4.AArch64.layout).artifact AArch64.target {
    notes := ["Baseline AArch64: ECB's key setup alone, for the modes: the masks of the round keys' planes, and the 32 round keys bitsliced into the table of the working space, in the order `decrypt` selects, as sixteen copies each."]
    code := Impl.Sm4.AArch64.prepareKeys
    verified := Proof.Sm4.AArch64.prepare_verified },
  (Spec.Sm4.Prepared.cryptApi Impl.Sm4.AArch64.layout).artifact AArch64.target {
    notes := ["Baseline AArch64: ECB's sixteen blocks alone, for the modes: bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, under the table `vg_sm4_prepare_keys` wrote."]
    code := Impl.Sm4.AArch64.cryptPrepared
    verified := Proof.Sm4.AArch64.crypt_verified }]

end VG.Artifacts.Sm4.AArch64
