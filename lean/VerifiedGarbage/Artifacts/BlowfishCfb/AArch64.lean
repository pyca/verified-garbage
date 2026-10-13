module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
import Mathlib.Tactic.SplitIfs

/-! # Blowfish-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.AArch64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline AArch64: through the batch of sixteen blocks of `vg_blowfish_ecb_encrypt` (inlined), one block \
  per batch: each S-box lookup is `tbl`/`tbx` over the whole box in AdvSIMD registers, so no address depends \
  on the key or the data; the schedule is read where it is. The mode is the generic CFB of \
  `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.Blowfish.cfbEncryptApi with
    target := AArch64.target
    doc := Spec.Blowfish.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncrypt
    contract := Spec.Blowfish.cfbEncryptContract AArch64.abi 224
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.cfbDecryptApi with
    target := AArch64.target
    doc := Spec.Blowfish.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecrypt
    contract := Spec.Blowfish.cfbDecryptContract AArch64.abi 224
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.BlowfishCfb.AArch64
