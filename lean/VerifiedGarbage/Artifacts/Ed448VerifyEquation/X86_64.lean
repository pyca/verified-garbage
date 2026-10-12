import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification's equation on x86-64

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

namespace VG.Artifacts.Ed448VerifyEquation.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.verifyEquationApi with
    target := X86_64.target
    doc := Spec.Ed448.verifyEquationApi.doc (notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in one word of `scratch`, 0 exactly when \
      all pass. Decodes R, then A, by one loop running the decoding twice, with RFC 8032's \
      square root (X448's addition chain up to z^(2^223 - 1), by a call of \
      `vg_gf448_r64_pow223`, then 223 squarings), and \
      negates A; computes [S]B + [k](-A) in 114 four-bit windows sharing four \
      doublings. Each window scans sixteen affine multiples of B and sixteen projective \
      multiples of -A, adding one of each. The latter table is built with fifteen affine \
      additions, without inversions, in scratch bytes 4096–7167. Doublings and affine \
      additions call the existing point functions; projective addition uses the same \
      field operations. Compares [4] of the result with [4]R projectively. Field elements \
      are X448's seven 64-bit words, multiplied with `mul` by columns. Callee-saved \
      registers are saved in the first 48 bytes of `scratch`."])
    code := Impl.Ed448.X86_64.verifyEquation
    contract := Spec.Ed448.verifyEquationContract X86_64.abi 8
    stack := 8
    verified := Proof.Ed448.X86_64.verifyEquation_verified Proof.Ed448.recover_ok
      Proof.Ed448.verifyEq_ok
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448VerifyEquation.X86_64
