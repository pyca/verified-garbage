import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.Pow250Verified
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnVerified

/-! # Products and powers in curve25519's field, in radix `2^16`, on ARMv7 -/

namespace VG.Artifacts.Gf25519R16.Arm

open VG.Spec.X25519.Field16 VG.Impl.Ed25519.Arm VG.Proof.Ed25519.Arm.Pow250

/-- How the function works. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `r4` to `r10` \
  in its own working space and runs the addition chain of ref10's `fe_invert` up to \
  `a^(2^250 - 1)` (249 squarings, most in loops counted by `r10`, and 10 multiplications) as the \
  ARMv7 Ed25519 code inlined it, with X25519's ARMv7 product (row by row, with only the low \
  32-bit `mul`, then `lo + 38 hi` and the carry folded in) and its two temporaries in bytes 1088 \
  to 1215. It then restores the registers."]

/-- How the product works. -/
def mulNotes : List String := ["Uses baseline integer instructions. The function saves `r4` to \
  `r11` in its own working space and runs X25519's ARMv7 product (row by row, with only the low \
  32-bit `mul`, into 32 limbs at byte 1472, then `lo + 38 hi` and the carry folded in twice) \
  with its operands and result through pointers: `ws` plus each offset. It then restores the \
  registers; it never writes `r12` or `lr`."]

def artifacts : List Artifact := [
  { mulApi with
    target := Arm.target
    doc := mulApi.doc (notes := mulNotes)
    code := mulFn
    contract := mulContract Arm.abi
    verified := Proof.Ed25519.Arm.Mul.mulFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { pow250Api with
    target := Arm.target
    doc := pow250Api.doc (notes := notes)
    code := pow250Fn
    contract := pow250Contract Arm.abi
    verified := pow250Fn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gf25519R16.Arm
