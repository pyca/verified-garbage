module

public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Seed.AArch64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: the 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, bitsliced in general-purpose registers through the AES S-box circuit."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey
    stack := 976
    verified := Proof.Seed.AArch64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64: calls `vg_seed_encrypt_blocks` with its working space on the stack, saving the link register in a 16-byte stack frame."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1088 .x3 136 (Impl.Seed.AArch64.ecbCall .encrypt)
    stack := 1104
    verified := Proof.Seed.AArch64.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64: calls `vg_seed_decrypt_blocks` with its working space on the stack, saving the link register in a 16-byte stack frame."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1088 .x3 136 (Impl.Seed.AArch64.ecbCall .decrypt)
    stack := 1104
    verified := Proof.Seed.AArch64.ecbCall_framed .decrypt },
  Spec.Seed.encryptBlocksApi.artifact AArch64.target {
    notes := ["Uses the first 976 bytes of `scratch`."]
    code := Impl.Seed.AArch64.encrypt
    stack := 0
    verified := Proof.Seed.AArch64.encrypt_blocks_verified },
  Spec.Seed.decryptBlocksApi.artifact AArch64.target {
    notes := ["Uses the first 976 bytes of `scratch`."]
    code := Impl.Seed.AArch64.decrypt
    stack := 0
    verified := Proof.Seed.AArch64.decrypt_blocks_verified }]

end VG.Artifacts.Seed.AArch64
