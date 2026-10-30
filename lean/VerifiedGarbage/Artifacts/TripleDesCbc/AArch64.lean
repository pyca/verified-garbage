module

public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
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
    notes := ["The DES kernel shared with TDEA-CMAC: rotated, spread halves, eight S-boxes looked up together in AdvSIMD registers with `tbl`, and grouped bit permutations. Round-key spreading, register tables and permutation masks are prepared once for all blocks. The 464-byte stack workspace is wiped on return."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 464 .x4 58 Impl.TripleDes.AArch64.TablesCbc.encrypt
    stack := 464
    verified := Proof.TripleDes.AArch64.TablesCbc.framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact AArch64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cbcDecryptChained
    stack := 1008
    verified := Proof.TripleDes.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.AArch64
