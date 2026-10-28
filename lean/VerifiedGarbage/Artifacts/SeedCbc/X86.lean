module

public import VerifiedGarbage.Proof.Seed.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.CbcLit

/-! # SEED-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), through `vg_seed_encrypt_blocks`, called on the block with the first 1088 bytes of the working space, its arguments pushed in a frame (20 bytes of stack with the return address). The mode is the generic CBC encryption of `Impl/Modes/X86/`, whose data pointer and steps left wait in `esi` and `ebp` across the call. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cbcEncryptChained
    stack := 1188
    verified := Proof.Seed.X86.Cbc.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time, through `vg_seed_decrypt_blocks`, called on the block with the first 1088 bytes of the working space, its arguments pushed in a frame (20 bytes of stack with the return address). The mode is the generic CBC decryption of `Impl/Modes/X86/`, whose data pointer and steps left wait in `esi` and `ebp` across the call. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cbcDecryptChained
    stack := 1188
    verified := Proof.Seed.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.X86
