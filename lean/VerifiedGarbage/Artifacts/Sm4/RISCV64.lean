module

public import VerifiedGarbage.Proof.Sm4.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.Verified
public import VerifiedGarbage.Proof.Sm4.RISCV64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit

/-! # SM4 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact RISCV64.target {
    notes := ["The key schedule's rounds bitsliced in general-purpose registers, sixteen copies of the \
        key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no \
        table lookups; the key is read and the schedule written a byte at a time. The working space \
        (3168 bytes, our caller's s0-s11 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 Impl.Sm4.RISCV64.expandKey
    stack := 3168
    verified := Proof.Sm4.RISCV64.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact RISCV64.target {
    notes := ["Sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box \
        circuit (SM4's S-box is an affine map of AES's), with no table lookups; the blocks and the \
        schedule are copied a byte at a time. Each round key's planes are made from its word: its \
        bytes spread to the planes' 16-bit groups, then each bit of a group filled to the group by \
        doubling. The working space (3168 bytes, our caller's s0-s11 among them) is on the stack, \
        zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .encrypt)
    stack := 3168
    verified := Proof.Sm4.RISCV64.ecb_framed .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact RISCV64.target {
    notes := ["Sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box \
        circuit (SM4's S-box is an affine map of AES's), with no table lookups; the blocks and the \
        schedule are copied a byte at a time. Each round key's planes are made from its word: its \
        bytes spread to the planes' 16-bit groups, then each bit of a group filled to the group by \
        doubling. The working space (3168 bytes, our caller's s0-s11 among them) is on the stack, \
        zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .decrypt)
    stack := 3168
    verified := Proof.Sm4.RISCV64.ecb_framed .decrypt },
  (Spec.Sm4.Prepared.prepareApi Impl.Sm4.RISCV64.layout).artifact RISCV64.target {
    notes := ["ECB's key setup alone, for the modes: the masks of the round keys' planes, and the 32 \
        round keys bitsliced into the table of the working space, in the order `decrypt` selects, as \
        sixteen copies each: each round key's bytes spread to the planes' 16-bit groups, then each \
        bit of a group filled to the group by doubling."]
    code := Impl.Sm4.RISCV64.prepareKeys
    verified := Proof.Sm4.RISCV64.prepare_verified },
  (Spec.Sm4.Prepared.cryptApi Impl.Sm4.RISCV64.layout).artifact RISCV64.target {
    notes := ["ECB's sixteen blocks alone, for the modes: bitsliced in general-purpose registers \
        through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
        lookups, under the table `vg_sm4_prepare_keys` wrote."]
    code := Impl.Sm4.RISCV64.cryptPrepared
    verified := Proof.Sm4.RISCV64.crypt_verified }]

end VG.Artifacts.Sm4.RISCV64
