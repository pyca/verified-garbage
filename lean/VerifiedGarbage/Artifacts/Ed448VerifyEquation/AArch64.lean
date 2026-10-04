import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification's equation on AArch64

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

namespace VG.Artifacts.Ed448VerifyEquation.AArch64

def artifacts : List Artifact := [
  { Spec.Ed448.verifyEquationApi with
    target := AArch64.target
    doc := Spec.Ed448.verifyEquationApi.doc (notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in `x20`, 0 exactly when all pass. Decodes A \
      with RFC 8032's square root (X448's addition chain up to z^(2^223 - 1), then 223 \
      squarings) and negates it; computes [S]B + [k](-A) with one chain of doublings, adding B \
      and -A for every bit of S and k and swapping each sum in with a mask of the bit; then \
      compares [4] of it with [4]R projectively. Field elements are eight 56-bit limbs, \
      multiplied by columns and reduced with `2^448 = 2^224 + 1` (mod p); comparisons and low \
      bits use the fully reduced value. The function saves `x19` and `x20` in the first 16 \
      bytes of `scratch`."])
    code := Impl.Ed448.AArch64.verifyEquation
    contract := Spec.Ed448.verifyEquationContract AArch64.abi
    verified := Proof.Ed448.AArch64.verifyEquation_verified Proof.Ed448.recover_ok
      Proof.Ed448.verifyEq_ok
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448VerifyEquation.AArch64
