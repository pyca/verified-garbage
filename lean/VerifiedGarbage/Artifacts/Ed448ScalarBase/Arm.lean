import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.BaseVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 base-point multiplication on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

namespace VG.Artifacts.Ed448ScalarBase.Arm

def artifacts : List Artifact := [
  { Spec.Ed448.scalarBaseApi with
    target := Arm.target
    doc := Spec.Ed448.scalarBaseApi.doc (notes := ["Expands the scalar's 456 bits into \
      bytes, then for each bit from the top doubles `R` and adds the base point to it with \
      RFC 8032's projective formulas, and swaps the sum into `R` with a mask of the bit: the \
      same operations for every bit. Field elements are X448's twenty-eight 16-bit limbs, \
      multiplied with the low 32-bit `mul`; `Z` is inverted with X448's addition chain for \
      `p - 2`. Callee-saved registers are saved in the first 32 bytes of `scratch`."])
    code := Impl.Ed448.Arm.scalarBase
    contract := Spec.Ed448.scalarBaseContract Arm.abi
    verified := Proof.Ed448.Arm.scalarBase_verified Proof.Ed448.baseLadder_ok
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448ScalarBase.Arm
