module

public import VerifiedGarbage.Proof.Camellia.X86.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86.Verified
import VerifiedGarbage.Proof.Camellia.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86.target {
    notes := ["Baseline IA-32: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 32-bit words."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2708 3 672 Impl.Camellia.X86.expandKey
    stack := 2708
    verified := Proof.Camellia.X86.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact X86.target {
    notes := ["Bitsliced on baseline IA-32: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .encrypt)
    stack := 2712
    verified := Proof.Camellia.X86.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact X86.target {
    notes := ["Bitsliced on baseline IA-32: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .decrypt)
    stack := 2712
    verified := Proof.Camellia.X86.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.X86
