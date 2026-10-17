module

public import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.AArch64

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the generic CBC of `Impl/Modes/AArch64/` over CAST5's ECB \
  block code (inlined): each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys are read where the caller passed them and the number of rounds \
  stays in `x1`; the 112-byte working space on the stack is zeroed on return."

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact AArch64.target {
    notes := [note, "The IV's address is kept in `x25`, which the core keeps, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcEncryptChained
    stack := 112
    verified := Proof.Cast5.AArch64.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact AArch64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcDecryptChained
    stack := 112
    verified := Proof.Cast5.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.AArch64
