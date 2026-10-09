import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.X25519.Arm.Field16
import VerifiedGarbage.Proof.X25519.Arm.Field16.Verified

/-! # Multiplication in curve25519's field, in radix `2^16`, on ARMv7 -/

namespace VG.Artifacts.Gf25519R16.Arm

open VG.Spec.X25519.Field16 VG.Impl.X25519.Arm.Field16 VG.Proof.X25519.Arm.Field16

/-- How the function works. -/
def notes : List String := ["Uses baseline integer instructions, multiplying with `mul` only. The \
  function saves `r4`–`r9` and `lr` in its own working space, keeps `o` in `lr`, and reads the \
  operands through pointers, as X25519's ARMv7 code does: the 32 limbs of the product row by row, \
  each row's carries propagated so that every sum fits in a word, folded with `2^256 = 38` into 16 \
  limbs, then the carry out folded in twice. It copies the result to `o` and restores the \
  registers. It never writes `r0`, `r10` or `r11`."]

def artifacts : List Artifact := [
  { mulApi with
    target := Arm.target
    doc := mulApi.doc (notes := notes)
    code := mulFn
    contract := mulContract Arm.abi
    verified := gf25519_mul_verified
    ofSig := by unfold mulContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gf25519R16.Arm
