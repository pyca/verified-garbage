import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.Point16Verified

/-! # Ed25519's point addition and doubling, in radix `2^16`, on ARMv7 -/

namespace VG.Artifacts.Ed25519R16.Arm

open VG.Spec.Ed25519.Point16 VG.Impl.Ed25519.Arm.Point16 VG.Proof.Ed25519.Arm.Point16

/-- How the functions work. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `r4` to `r9` \
  in its own working space and runs the complete addition formula as the ARMv7 Ed25519 code \
  inlined it: nine products of sixteen-limb field elements, by X25519's ARMv7 product (row by \
  row, with only the low 32-bit `mul`, then `lo + 38 hi` and the carry folded in), and \
  additions and subtractions, with the temporaries in bytes 576 to 1087. It then restores the \
  registers."]

def artifacts : List Artifact := [
  { addApi with
    target := Arm.target
    doc := addApi.doc (notes := notes)
    code := addFn
    contract := addContract Arm.abi
    verified := addFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { doubleApi with
    target := Arm.target
    doc := doubleApi.doc (notes := notes)
    code := doubleFn
    contract := doubleContract Arm.abi
    verified := doubleFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519R16.Arm
