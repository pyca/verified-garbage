module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4 artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact PPC64LE.target {
    notes := ["The key schedule's rounds bitsliced in general-purpose registers, sixteen copies of the \
        key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no \
        table lookups. The working space (3216 bytes, our caller's r14-r31 among them) is on the \
        stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r5 402 Impl.Sm4.PPC64LE.expandKey
    stack := 3248
    verified := Proof.Sm4.PPC64LE.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact PPC64LE.target {
    notes := ["Sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box \
        circuit (SM4's S-box is an affine map of AES's), with no table lookups. The working space \
        (3216 bytes, our caller's r14-r31 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .encrypt)
    stack := 3248
    verified := Proof.Sm4.PPC64LE.ecb_framed .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact PPC64LE.target {
    notes := ["Sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box \
        circuit (SM4's S-box is an affine map of AES's), with no table lookups. The working space \
        (3216 bytes, our caller's r14-r31 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .decrypt)
    stack := 3248
    verified := Proof.Sm4.PPC64LE.ecb_framed .decrypt },
  (Spec.Sm4.Prepared.prepareApi Impl.Sm4.PPC64LE.layout).artifact PPC64LE.target {
    notes := ["ECB's key setup alone, for the modes: the masks of the round keys' planes, and the 32 \
        round keys bitsliced into the table of the working space, in the order `decrypt` selects, as \
        sixteen copies each."]
    code := Impl.Sm4.PPC64LE.prepareKeys
    verified := Proof.Sm4.PPC64LE.prepare_verified },
  (Spec.Sm4.Prepared.cryptApi Impl.Sm4.PPC64LE.layout).artifact PPC64LE.target {
    notes := ["ECB's sixteen blocks alone, for the modes: bitsliced in general-purpose registers \
        through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
        lookups, under the table `vg_sm4_prepare_keys` wrote."]
    code := Impl.Sm4.PPC64LE.cryptPrepared
    verified := Proof.Sm4.PPC64LE.crypt_verified }]

end VG.Artifacts.Sm4.PPC64LE
