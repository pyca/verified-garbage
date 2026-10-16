module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

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
  Spec.Blowfish.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.BlowfishCfb.AArch64
