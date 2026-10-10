import VerifiedGarbage.Proof.Camellia.AArch64.CtrVerified

/-! # Camellia-CTR artifacts on baseline AArch64 -/

namespace VG.Artifacts.CamelliaCtr.AArch64

def artifacts : List Artifact := [
  { Spec.Camellia.ctrApi with
    target := AArch64.target
    doc := Spec.Camellia.ctrApi.doc
      (notes := ["Baseline AArch64: eight counter blocks at a time, encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call. The mode is the generic CTR of `Impl/Modes/AArch64/`, over Camellia's ECB core."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.ctr
    contract := Spec.Camellia.ctrContract AArch64.abi 3248
    stack := 3248
    verified := Proof.Camellia.AArch64.ctr_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CamelliaCtr.AArch64
