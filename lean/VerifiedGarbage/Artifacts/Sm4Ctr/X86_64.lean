import VerifiedGarbage.Proof.Sm4.X86_64.CtrVerified

/-! # SM4-CTR artifacts on baseline x86-64 -/

namespace VG.Artifacts.Sm4Ctr.X86_64

def artifacts : List Artifact := [
  { Spec.Sm4.ctrApi with
    target := X86_64.target
    doc := Spec.Sm4.ctrApi.doc
      (notes := ["Baseline x86-64: sixteen counter blocks at a time, encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 Impl.Sm4.X86_64.ctr
    contract := Spec.Sm4.ctrContract X86_64.abi 3144
    stack := 3144
    verified := Proof.Sm4.X86_64.ctr_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Sm4Ctr.X86_64
