import VerifiedGarbage.Proof.Idea.Arm.Verified

/-! # IDEA artifacts on baseline ARMv7 -/

namespace VG.Artifacts.Idea.Arm

def artifacts : List Artifact := [
  { Spec.Idea.expandKeyApi with
    target := Arm.target
    doc := Spec.Idea.expandKeyApi.doc
      (notes := ["Baseline ARMv7: each 32-bit word of subkeys is a fixed bit permutation of the key's four words, assembled with rotations and masks, without branches."])
    code := Impl.Idea.Arm.expandKey
    contract := Spec.Idea.expandKeyContract Arm.abi
    stack := 0
    verified := Proof.Idea.Arm.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.invertKeyApi with
    target := Arm.target
    doc := Spec.Idea.invertKeyApi.doc
      (notes := ["Baseline ARMv7: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."])
    code := Impl.StackScratch.Arm.withRegScratch 24 .r2 Impl.Idea.Arm.invertKey
    contract := Spec.Idea.invertKeyContract Arm.abi 24
    stack := 24
    verified := Proof.Idea.Arm.invertKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.ecbApi with
    target := Arm.target
    doc := Spec.Idea.ecbApi.doc
      (notes := ["Baseline ARMv7, a block at a time in general-purpose registers: each multiplication modulo 2^16 + 1 is a 32-bit `mul` of the residues and a reduction of the product less one, without branches."])
    code := Impl.StackScratch.Arm.withRegScratch 32 .r3 Impl.Idea.Arm.ecb
    contract := Spec.Idea.ecbContract Arm.abi 32
    stack := 32
    verified := Proof.Idea.Arm.ecb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Idea.Arm
