import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified

/-! # SM4-OFB artifacts on baseline AArch64 -/

namespace VG.Artifacts.Sm4Ofb.AArch64

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
  lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is \
  built once per call. The mode is the generic OFB of `Impl/Modes/AArch64/`, over SM4's ECB core, with the IV's \
  address kept in a vector register across the core's code."

def artifacts : List Artifact := [
  { Spec.Sm4.ofbApi with
    target := AArch64.target
    doc := Spec.Sm4.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.ofb
    contract := Spec.Sm4.ofbContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Ofb.AArch64
