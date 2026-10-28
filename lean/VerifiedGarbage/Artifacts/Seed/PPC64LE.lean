module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit

/-! # SEED artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Seed.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact PPC64LE.target {
    notes := ["The 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, \
        bitsliced in general-purpose registers through the AES S-box circuit, with no table lookups. \
        The working space (1040 bytes, our caller's r14-r31 among them) is on the stack, zeroed \
        before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey
    stack := 1072
    verified := Proof.Seed.PPC64LE.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact PPC64LE.target {
    notes := ["Calls `vg_seed_encrypt_blocks` with its working space (1088 bytes) on the stack, zeroed \
        before returning, saving the link register in a 48-byte stack frame."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .encrypt)
    stack := 1168
    verified := Proof.Seed.PPC64LE.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact PPC64LE.target {
    notes := ["Calls `vg_seed_decrypt_blocks` with its working space (1088 bytes) on the stack, zeroed \
        before returning, saving the link register in a 48-byte stack frame."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .decrypt)
    stack := 1168
    verified := Proof.Seed.PPC64LE.ecbCall_framed .decrypt },
  Spec.Seed.encryptBlocksApi.artifact PPC64LE.target {
    notes := ["Sixteen blocks at a time, each round's `G` of all of them bitsliced in general-purpose registers \
        through the AES S-box circuit, with no table lookups. Uses the first 1040 bytes of `scratch`, our \
        caller's r14-r31 among them, saved around each batch's rounds."]
    code := Impl.Seed.PPC64LE.encrypt
    stack := 0
    verified := Proof.Seed.PPC64LE.encrypt_blocks_verified },
  Spec.Seed.decryptBlocksApi.artifact PPC64LE.target {
    notes := ["Sixteen blocks at a time, each round's `G` of all of them bitsliced in general-purpose registers \
        through the AES S-box circuit, with no table lookups. Uses the first 1040 bytes of `scratch`, our \
        caller's r14-r31 among them, saved around each batch's rounds."]
    code := Impl.Seed.PPC64LE.decrypt
    stack := 0
    verified := Proof.Seed.PPC64LE.decrypt_blocks_verified }]

end VG.Artifacts.Seed.PPC64LE
