import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification's equation on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

namespace VG.Artifacts.Ed448VerifyEquation.X86

def artifacts : List Artifact := [
  { Spec.Ed448.verifyEquationApi with
    target := X86.target
    doc := Spec.Ed448.verifyEquationApi.doc (notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in one word of `scratch`, 0 exactly when \
      all pass. Decodes R, then A, by one loop running the decoding twice, with RFC 8032's \
      square root (X448's addition chain up to z^(2^223 - 1), then 223 squarings), and \
      negates A; computes [S]B + [k](-A) with one \
      chain of doublings, adding B and -A for every bit of S and k and swapping each sum in \
      with a mask of the bit; then compares [4] of it with [4]R projectively. Field elements \
      are X448's twenty-eight 16-bit limbs in `scratch`, and the field arithmetic is by calls \
      of `vg_gf448_r16_mul`, `vg_gf448_r16_add` and `vg_gf448_r16_sub`. Callee-saved \
      registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.Ed448.X86.verifyEquation
    contract := Spec.Ed448.verifyEquationContract X86.abi 20
    stack := 20
    verified := Proof.Ed448.X86.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448VerifyEquation.X86
