import VerifiedGarbage.Proof.Cast5.X86.ModesVerified

/-! # CAST5-OFB artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.Cast5Ofb.X86

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, through the generic OFB of `Impl/Modes/X86/` over CAST5's ECB \
  block code: each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys and the number of rounds are reloaded from the arguments for each block."

def artifacts : List Artifact := [
  { Spec.Cast5.ofbApi with
    target := X86.target
    doc := Spec.Cast5.ofbApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofb
    contract := Spec.Cast5.ofbContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336
    stack := 336
    verified := Proof.Cast5.X86.ModeFns.ofb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Cast5Ofb.X86
