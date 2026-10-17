module

public import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit

/-! # Triple DES-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86_64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block` \
  and `vg_triple_des_decrypt_block`'s code, inlined), with Boolean S-box circuits and no table lookups; \
  the schedule is copied into the working space once per call. The mode is the generic CBC of \
  `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86_64.target {
    notes := [note, "The IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained
    stack := 984
    verified := Proof.TripleDes.X86_64.cbcEncryptChained_framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86_64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcDecryptChained
    stack := 984
    verified := Proof.TripleDes.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.X86_64
