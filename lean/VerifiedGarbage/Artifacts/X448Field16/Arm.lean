module

public import VerifiedGarbage.Proof.X448.Arm.FnVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Arithmetic in curve448's field, in radix `2^16`, on ARMv7 -/

@[expose] public section

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
  mulApi.artifact Arm.target {
    notes := notes
    code := mulFn
    verified := gf448_mul_verified },
  addApi.artifact Arm.target {
    notes := notes
    code := addFn
    verified := gf448_add_verified },
  subApi.artifact Arm.target {
    notes := notes
    code := subFn
    verified := gf448_sub_verified },
  mulA24Api.artifact Arm.target {
    notes := notes
    code := mulA24Fn
    verified := gf448_mulA24_verified }]

end VG.Artifacts.X448Field16.Arm
