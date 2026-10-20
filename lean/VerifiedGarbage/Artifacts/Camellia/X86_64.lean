module

public import VerifiedGarbage.Proof.Camellia.X86_64.Verified
public import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.PreparedVerified
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Camellia.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 64-bit words."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey
    stack := 3216
    verified := Proof.Camellia.X86_64.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact X86_64.target {
    notes := ["Bitsliced on baseline x86-64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401
      (Impl.Camellia.X86_64.ecb .encrypt)
    stack := 3216
    verified := Proof.Camellia.X86_64.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact X86_64.target {
    notes := ["Bitsliced on baseline x86-64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401
      (Impl.Camellia.X86_64.ecb .decrypt)
    stack := 3216
    verified := Proof.Camellia.X86_64.ecb_framed .decrypt },
  (Spec.Camellia.Prepared.cryptApi Impl.Camellia.X86_64.layout).artifact X86_64.target {
    notes := ["Baseline x86-64: ECB's eight blocks alone, for the modes: bitsliced in general-purpose registers, each half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table lookups, under the table of bitsliced subkeys in the working space."]
    code := Impl.Camellia.X86_64.cryptPrepared
    verified := Proof.Camellia.X86_64.crypt_verified }]

end VG.Artifacts.Camellia.X86_64
