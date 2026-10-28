module

public import VerifiedGarbage.Proof.Seed.X86_64.Frame
public import VerifiedGarbage.Proof.Seed.X86_64.EcbCall
public import VerifiedGarbage.Proof.Seed.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-! # SEED artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86_64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64: the 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, bitsliced in general-purpose registers through the AES S-box circuit, grouping the affine layer's parity-specific XOR sums before masking."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey
    stack := 1064
    verified := Proof.Seed.X86_64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact X86_64.target {
    notes := ["Baseline x86-64: calls `vg_seed_encrypt_blocks` with its working space on the stack."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .encrypt)
    stack := 1104
    verified := Proof.Seed.X86_64.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact X86_64.target {
    notes := ["Baseline x86-64: calls `vg_seed_decrypt_blocks` with its working space on the stack."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .decrypt)
    stack := 1104
    verified := Proof.Seed.X86_64.ecbCall_framed .decrypt },
  Spec.Seed.encryptBlocksApi.artifact X86_64.target {
    notes := ["Baseline x86-64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), grouping the affine layer's parity-specific XOR sums before masking, with no table lookups. Uses the first 1056 bytes of `scratch`."]
    code := Impl.Seed.X86_64.encrypt
    stack := 0
    verified := Proof.Seed.X86_64.encrypt_blocks_verified },
  Spec.Seed.decryptBlocksApi.artifact X86_64.target {
    notes := ["Baseline x86-64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), grouping the affine layer's parity-specific XOR sums before masking, with no table lookups. Uses the first 1056 bytes of `scratch`."]
    code := Impl.Seed.X86_64.decrypt
    stack := 0
    verified := Proof.Seed.X86_64.decrypt_blocks_verified }]

end VG.Artifacts.Seed.X86_64
