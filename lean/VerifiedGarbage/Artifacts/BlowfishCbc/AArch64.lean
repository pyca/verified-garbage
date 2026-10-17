module

public import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.AArch64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline AArch64: sixteen blocks at a time, through the batch of `vg_blowfish_ecb_encrypt` and \
  `vg_blowfish_ecb_decrypt` (inlined): each S-box lookup is `tbl`/`tbx` over the whole box in AdvSIMD \
  registers, so no address depends on the key or the data; the schedule is read where it is. Decryption \
  deciphers sixteen blocks per batch; encryption, which is sequential, one. The mode is the generic CBC of \
  `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact AArch64.target {
    notes := [note, "The IV's address is kept in `x25`, which the core keeps, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcEncryptChained
    stack := 224
    verified := Proof.Blowfish.AArch64.cbcEncryptChained_framed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact AArch64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcDecryptChained
    stack := 224
    verified := Proof.Blowfish.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.BlowfishCbc.AArch64
