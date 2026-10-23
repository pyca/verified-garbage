module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Verified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Camellia.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact PPC64LE.target {
    notes := ["`KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the \
        value; the subkeys as rotations of 64-bit words, stored byte-swapped with `stdbrx`. The \
        working space (3312 bytes, our caller's r14-r31 among them) is on the stack, zeroed before \
        returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r6 414 Impl.Camellia.PPC64LE.expandKey
    stack := 3344
    verified := Proof.Camellia.PPC64LE.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact PPC64LE.target {
    notes := ["Bitsliced: 8 blocks at a time in general-purpose registers, copied through the working \
        space, each half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table \
        lookups. The working space (3312 bytes, our caller's r14-r31 among them) is on the stack, \
        zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414
      (Impl.Camellia.PPC64LE.ecb .encrypt)
    stack := 3344
    verified := Proof.Camellia.PPC64LE.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact PPC64LE.target {
    notes := ["Bitsliced: 8 blocks at a time in general-purpose registers, copied through the working \
        space, each half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table \
        lookups; the subkeys bitsliced in decryption's order, then encryption's rounds. The working \
        space (3312 bytes, our caller's r14-r31 among them) is on the stack, zeroed before \
        returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414
      (Impl.Camellia.PPC64LE.ecb .decrypt)
    stack := 3344
    verified := Proof.Camellia.PPC64LE.ecb_framed .decrypt },
  (Spec.Camellia.Prepared.prepareApi Impl.Camellia.PPC64LE.layout).artifact PPC64LE.target {
    notes := ["ECB's key setup alone, for the modes: the masks of the layers and the subkeys of 18 or \
        24 rounds bitsliced into the table of the working space, in the order `decrypt` selects, as \
        eight copies each."]
    code := Impl.Camellia.PPC64LE.prepareKeys
    verified := Proof.Camellia.PPC64LE.prepare_verified },
  (Spec.Camellia.Prepared.cryptApi Impl.Camellia.PPC64LE.layout).artifact PPC64LE.target {
    notes := ["ECB's eight blocks alone, for the modes: bitsliced in general-purpose registers, each \
        half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table lookups, under \
        the table `vg_camellia_prepare_keys` wrote."]
    code := Impl.Camellia.PPC64LE.cryptPrepared
    verified := Proof.Camellia.PPC64LE.crypt_verified }]

end VG.Artifacts.Camellia.PPC64LE
