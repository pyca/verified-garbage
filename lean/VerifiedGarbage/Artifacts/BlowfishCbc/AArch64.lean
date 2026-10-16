module

public import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Lit
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
  Spec.Blowfish.cbcEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcEncrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cbcEncrypt_framed },
  Spec.Blowfish.cbcDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcDecrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cbcDecrypt_framed }]

end VG.Artifacts.BlowfishCbc.AArch64
