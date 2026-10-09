import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified

/-! The complete strict verification equation on baseline i686. -/
namespace VG.Artifacts.Ed25519Verify.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := X86.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Checks canonical point encodings (A's, then R's, by one loop running \
      the decoding twice) and S < L, then evaluates the uncofactored equation using all 512 challenge bits. \
      Computes [k]A - [S]B with one chain of doublings and 4-bit windows of the public \
      scalars, from a table of [1]A to [15]A and constant -[1]B to -[15]B, skipping the \
      leading zero bytes of k above its low 32, and compares it with -R projectively. \
      Point tables and callee-saved registers reside in `scratch`; field products call \
      `vg_gf25519_r32_mul`."])
    code := Impl.Ed25519.X86.verifyEquation
    contract := Spec.Ed25519.verifyEquationContract X86.abi 20
    verified := Proof.Ed25519.X86.verify_verified
    stack := 20
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519Verify.X86
