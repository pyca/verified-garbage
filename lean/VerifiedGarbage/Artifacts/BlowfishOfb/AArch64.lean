module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Blowfish-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.AArch64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline AArch64: through the batch of sixteen blocks of `vg_blowfish_ecb_encrypt` (inlined), one block \
  per batch: each S-box lookup is `tbl`/`tbx` over the whole box in AdvSIMD registers, so no address depends \
  on the key or the data; the schedule is read where it is. The mode is the generic OFB of \
  `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.Blowfish.ofbApi with
    target := AArch64.target
    doc := Spec.Blowfish.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.ofb
    contract := Spec.Blowfish.ofbContract AArch64.abi 224
    stack := 224
    verified := Proof.Blowfish.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.BlowfishOfb.AArch64
