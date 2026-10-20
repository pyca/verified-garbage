module

public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.AArch64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block` \
  and `vg_triple_des_decrypt_block`'s code, inlined), with Boolean S-box circuits and no table lookups; \
  the schedule is copied into the working space once per call. The mode is the generic CBC of \
  `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact AArch64.target {
    notes := [note, "The IV's address is kept in `x25`, which the core keeps, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cbcEncryptChained
    stack := 1008
    verified := Proof.TripleDes.AArch64.cbcEncryptChained_framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact AArch64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cbcDecryptChained
    stack := 1008
    verified := Proof.TripleDes.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.AArch64
