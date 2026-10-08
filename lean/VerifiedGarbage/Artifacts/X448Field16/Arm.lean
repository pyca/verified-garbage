import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.X448.Arm
import VerifiedGarbage.Proof.X448.Arm.FnVerified

/-! # Arithmetic in curve448's field, in radix `2^16`, on ARMv7 -/

namespace VG.Artifacts.X448Field16.Arm

open VG.Spec.X448.Field16 VG.Impl.X448.Arm VG.Proof.X448.Arm

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r7`, `r9` and `lr` in its own working \
  space and reads the operands and writes the result through pointers. The product is computed \
  row by row with `mul`, each row's carries propagated so that every sum fits in a word, into \
  56 limbs in the own working space, folded with `2^448 = 2^224 + 1` (mod p); the sum, the \
  difference (`a + 2p - b`) and the product by 39081 are computed limb by limb there. Three \
  carry passes, with the carry out folded into limbs 0 and 14, then bring every limb below \
  `2^16`. It never writes `r0`, `r8`, `r10` or `r11`."]

def artifacts : List Artifact := [
  { mulApi with
    target := Arm.target
    doc := mulApi.doc (notes := notes)
    code := mulFn
    contract := mulContract Arm.abi
    verified := gf448_mul_verified
    ofSig := by unfold mulContract binContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { addApi with
    target := Arm.target
    doc := addApi.doc (notes := notes)
    code := addFn
    contract := addContract Arm.abi
    verified := gf448_add_verified
    ofSig := by unfold addContract binContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { subApi with
    target := Arm.target
    doc := subApi.doc (notes := notes)
    code := subFn
    contract := subContract Arm.abi
    verified := gf448_sub_verified
    ofSig := by unfold subContract binContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { mulA24Api with
    target := Arm.target
    doc := mulA24Api.doc (notes := notes)
    code := mulA24Fn
    contract := mulA24Contract Arm.abi
    verified := gf448_mulA24_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X448Field16.Arm
