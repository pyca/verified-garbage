module

public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyVerified
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
# Ed448 verification's equation on AArch64

The signature and documentation come from the reviewed Ed448 API. Decoding's
agreement with the specification (`Proof/Ed448/Facts.lean`) is passed to the
proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.AArch64

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact AArch64.target {
    notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in `x20`, 0 exactly when all pass. Decodes A \
      with RFC 8032's square root (X448's addition chain up to z^(2^223 - 1), then 223 \
      squarings) and negates it. Computes [S]B with `vg_ed448_scalar_base`'s comb of 57 tables \
      (a call of `vg_ed448_r56_comb_base`, and `16 A + B` by calls of `vg_ed448_r56_point_add`), \
      and [k](-A) with 4-bit windows of k from the top: four doublings, then the addition of \
      [n](-A) for the window's digit n, selected with masks from all 16 entries of a table built \
      in `scratch`. Then compares [4]([S]B + [k](-A)) with [4]R projectively. Field elements \
      are eight 56-bit limbs, multiplied as `vg_x448`'s are; comparisons and low bits use the \
      fully reduced value. The function copies the challenge into `scratch`, and saves its \
      caller's callee-saved registers there."]
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.verifyEquation
    verified := Proof.Ed448.AArch64.verifyEquation_verified Proof.Ed448.recover_ok }]

end VG.Artifacts.Ed448VerifyEquation.AArch64
