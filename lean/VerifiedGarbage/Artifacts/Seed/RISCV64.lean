module

public import VerifiedGarbage.Proof.Seed.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.Lit

/-! # SEED artifacts on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Seed.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact RISCV64.target {
    notes := ["The 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, \
        bitsliced in general-purpose registers through the AES S-box circuit, with no table lookups. \
        The working space (1032 bytes, our caller's s0-s11 among them) is on the stack, zeroed \
        before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a2 129 Impl.Seed.RISCV64.expandKey
    stack := 1040
    verified := Proof.Seed.RISCV64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact RISCV64.target {
    notes := ["Sixteen blocks at a time, each round's `G` of all of them bitsliced in general-purpose registers \
        through the AES S-box circuit, with no table lookups. The working space (1032 bytes, our \
        caller's s0-s11 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .encrypt)
    stack := 1040
    verified := Proof.Seed.RISCV64.ecb_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact RISCV64.target {
    notes := ["Sixteen blocks at a time, each round's `G` of all of them bitsliced in general-purpose registers \
        through the AES S-box circuit, with no table lookups. The working space (1032 bytes, our \
        caller's s0-s11 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .decrypt)
    stack := 1040
    verified := Proof.Seed.RISCV64.ecb_framed .decrypt }]

end VG.Artifacts.Seed.RISCV64
