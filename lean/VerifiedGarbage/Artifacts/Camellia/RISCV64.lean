module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Verified
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit

/-! # Camellia artifacts on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Camellia.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact RISCV64.target {
    notes := ["`KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the \
        value; the subkeys as rotations of 64-bit words, stored big-endian a byte at a time. The \
        working space (3200 bytes, our caller's s0-s11 among them) is on the stack, zeroed before \
        returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a3 400 Impl.Camellia.RISCV64.expandKey
    stack := 3200
    verified := Proof.Camellia.RISCV64.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact RISCV64.target {
    notes := ["Bitsliced: 8 blocks at a time in general-purpose registers, copied through the working \
        space, each half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table \
        lookups. The working space (3200 bytes, our caller's s0-s11 among them) is on the stack, \
        zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400
      (Impl.Camellia.RISCV64.ecb .encrypt)
    stack := 3200
    verified := Proof.Camellia.RISCV64.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact RISCV64.target {
    notes := ["Bitsliced: 8 blocks at a time in general-purpose registers, copied through the working \
        space, each half as eight 64-bit planes, the S-boxes as Boolean circuits, with no table \
        lookups; the subkeys bitsliced in decryption's order, then encryption's rounds. The working \
        space (3200 bytes, our caller's s0-s11 among them) is on the stack, zeroed before \
        returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400
      (Impl.Camellia.RISCV64.ecb .decrypt)
    stack := 3200
    verified := Proof.Camellia.RISCV64.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.RISCV64
