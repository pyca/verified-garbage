module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.VVerified
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
# Ed448 verification's equation on RISC-V

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact RISCV64.target {
    notes := ["Uses only caller-saved registers and no stack, and runs the same operations whatever \
      the inputs: the checks (the encodings of A and R, S < L, and the final comparison) are \
      accumulated in a doubleword of `scratch`, 0 exactly when all pass. Decodes A and R with \
      RFC 8032's square root (square and multiply over the bits of (p - 3) / 4) and negates \
      them; then computes [4S]B + [4k](-A) + [4](-R) with four iterations of the same code per \
      bit, each RFC 8032's addition of a point selected with masks (the sum itself, B, -A or \
      -R) and the sum swapped in with a mask from a table of the bits; and checks that the \
      result is the neutral point. Field elements are fourteen 32-bit limbs in `scratch` \
      (rounded up to a multiple of 8), with `vg_x448`'s multiplication, addition and \
      subtraction."]
    code := Impl.Ed448.RISCV64.verifyEquation
    verified := Proof.Ed448.RISCV64.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq4_ok }]

end VG.Artifacts.Ed448VerifyEquation.RISCV64
