import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified

/-! # Camellia-CTR artifacts on baseline x86-64 -/

namespace VG.Artifacts.CamelliaCtr.X86_64

def artifacts : List Artifact := [
  { Spec.Camellia.ctrApi with
    target := X86_64.target
    doc := Spec.Camellia.ctrApi.doc
      (notes := ["Baseline x86-64: eight counter blocks at a time, encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call. The mode is the generic CTR of `Impl/Modes/X86_64/`, over Camellia's ECB core."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 Impl.Camellia.X86_64.ctr
    contract := Spec.Camellia.ctrContract X86_64.abi 3216
    stack := 3216
    verified := Proof.Camellia.X86_64.ctr_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CamelliaCtr.X86_64
