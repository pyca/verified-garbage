module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified

/-! # CAST5-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.AArch64

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the generic OFB of `Impl/Modes/AArch64/` over CAST5's ECB \
  block code (inlined): each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys are read where the caller passed them and the number of rounds \
  stays in `x1`; the 112-byte working space on the stack is zeroed on return."

def artifacts : List Artifact := [
  { Spec.Cast5.ofbApi with
    target := AArch64.target
    doc := Spec.Cast5.ofbApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofb
    contract := Spec.Cast5.ofbContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112
    stack := 112
    verified := Proof.Cast5.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Cast5Ofb.AArch64
