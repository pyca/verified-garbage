import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified

/-! # SM4-CTR artifacts on baseline AArch64 -/

namespace VG.Artifacts.Sm4Ctr.AArch64

def artifacts : List Artifact := [
  { Spec.Sm4.ctrApi with
    target := AArch64.target
    doc := Spec.Sm4.ctrApi.doc
      (notes := ["Baseline AArch64: sixteen counter blocks at a time, encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.ctr
    contract := Spec.Sm4.ctrContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.ctr_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Ctr.AArch64
