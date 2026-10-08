import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification's equation on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

namespace VG.Artifacts.Ed448VerifyEquation.Arm

def artifacts : List Artifact := [
  { Spec.Ed448.verifyEquationApi with
    target := Arm.target
    doc := Spec.Ed448.verifyEquationApi.doc (notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in a register, 0 exactly when all pass. \
      Decodes A with RFC 8032's square root (X448's addition chain up to z^(2^223 - 1), then \
      223 squarings) and negates it; computes [S]B + [k](-A) with one chain of doublings, \
      adding B and -A for every bit of S and k and swapping each sum in with a mask of the \
      bit; then compares [4] of it with [4]R projectively. Field elements are X448's \
      twenty-eight 16-bit limbs; multiplications, additions and subtractions are calls of the \
      `vg_gf448_r16_*` functions on `scratch`. Callee-saved registers are saved in the first \
      32 bytes of `scratch`."])
    code := Impl.Ed448.Arm.verifyEquation
    contract := Spec.Ed448.verifyEquationContract Arm.abi
    verified := Proof.Ed448.Arm.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448VerifyEquation.Arm
