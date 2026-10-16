module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 verification's equation on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.Arm

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact Arm.target {
    notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in a register, 0 exactly when all pass. \
      Decodes A with RFC 8032's square root (X448's addition chain up to z^(2^223 - 1), then \
      223 squarings) and negates it; computes [S]B + [k](-A) with one chain of doublings, \
      adding B and -A for every bit of S and k and swapping each sum in with a mask of the \
      bit; then compares [4] of it with [4]R projectively. Field elements are X448's \
      twenty-eight 16-bit limbs; multiplications, additions and subtractions are calls of the \
      `vg_gf448_r16_*` functions on `scratch`. Callee-saved registers are saved in the first \
      32 bytes of `scratch`."]
    code := Impl.Ed448.Arm.verifyEquation
    verified := Proof.Ed448.Arm.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok
    stack := 0 }]

end VG.Artifacts.Ed448VerifyEquation.Arm
