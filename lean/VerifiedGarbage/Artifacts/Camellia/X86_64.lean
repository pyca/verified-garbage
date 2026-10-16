module

public import VerifiedGarbage.Proof.Camellia.X86_64.Verified
public import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
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
    verified := Proof.Camellia.X86_64.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.X86_64
