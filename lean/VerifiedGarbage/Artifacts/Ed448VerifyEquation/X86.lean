module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 verification's equation on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.X86

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact X86.target {
    notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in one word of `scratch`, 0 exactly when \
      all pass. Decodes R, then A, by one loop running the decoding twice, with RFC 8032's \
      square root (X448's addition chain up to z^(2^223 - 1), then 223 squarings), and \
      negates A; computes [S]B + [k](-A) with one \
      chain of doublings, adding B and -A for every bit of S and k and swapping each sum in \
      with a mask of the bit; then compares [4] of it with [4]R projectively. Field elements \
      are X448's twenty-eight 16-bit limbs in `scratch`, and the field arithmetic is by calls \
      of `vg_gf448_r16_mul`, `vg_gf448_r16_add` and `vg_gf448_r16_sub`. Callee-saved \
      registers are saved in the first 16 bytes of `scratch`."]
    code := Impl.Ed448.X86.verifyEquation
    stack := 20
    verified := Proof.Ed448.X86.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok }]

end VG.Artifacts.Ed448VerifyEquation.X86
