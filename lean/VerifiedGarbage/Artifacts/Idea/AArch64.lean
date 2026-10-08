import VerifiedGarbage.Proof.Idea.AArch64.Invert

/-! # IDEA artifacts on baseline AArch64 -/

namespace VG.Artifacts.Idea.AArch64

def artifacts : List Artifact := [
  { Spec.Idea.expandKeyApi with
    target := AArch64.target
    doc := Spec.Idea.expandKeyApi.doc
      (notes := ["Baseline AArch64: each quadword of subkeys is a fixed bit permutation of the key's two quadwords, assembled with rotations and masks, without branches."])
    code := Impl.Idea.AArch64.expandKey
    contract := Spec.Idea.expandKeyContract AArch64.abi
    stack := 0
    verified := Proof.Idea.AArch64.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.invertKeyApi with
    target := AArch64.target
    doc := Spec.Idea.invertKeyApi.doc
      (notes := ["Baseline AArch64: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."])
    code := Impl.Idea.AArch64.invertKey
    contract := Spec.Idea.invertKeyContract AArch64.abi
    stack := 0
    verified := Proof.Idea.AArch64.invertKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.ecbApi with
    target := AArch64.target
    doc := Spec.Idea.ecbApi.doc
      (notes := ["Baseline AArch64, a block at a time in general-purpose registers: each multiplication modulo 2^16 + 1 is a `mul` and a reduction without branches."])
    code := Impl.Idea.AArch64.ecb
    contract := Spec.Idea.ecbContract AArch64.abi 0
    stack := 0
    verified := Proof.Idea.AArch64.ecb_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Idea.AArch64
