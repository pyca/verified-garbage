module

public import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 verification's equation on x86-64

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448VerifyEquation

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := ["Uses the selected field backend and baseline integer instructions elsewhere, \
      and indexes the public-key table using public challenge digits. The checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in one word of `scratch`, 0 exactly when \
      all pass. Decodes R, then A, by one loop running the decoding twice, with RFC 8032's \
      square root (X448's addition chain up to z^(2^223 - 1), by a call of \
      `vg_gf448_r64_pow223`, then 223 squarings), and \
      negates A; computes [S]B + [k](-A) with width-five non-adjacent form digits, \
      sharing 461 doublings and skipping additions for zero public digits. The signed \
      byte streams occupy scratch bytes 3072–3532 and 3536–3996. Fixed-base selection scans seventeen affine multiples of B; public-key \
      selection reads only the indexed projective multiple of -A. The accumulator starts \
      at the identity. The latter table is built with sixteen affine \
      additions, without inversions, in scratch bytes 4096–7359. Doublings and additions call the selected point functions; \
      projective addition first forms Z1*Z2 and then reuses the affine formula. Compares [4] of the result with [4]R projectively. Field elements \
      are X448's seven 64-bit words, multiplied by the selected backend. Callee-saved \
      registers are saved in the first 48 bytes of `scratch`."]
    code := Impl.Ed448.X86_64.verifyEquationFor v
    stack := 8
    verified := Proof.Ed448.X86_64.verifyEquationFor_verified v Proof.Ed448.recover_ok
      Proof.Ed448.verifyEq_ok }]

end VG.Generic.Curve448Field.X86_64.Ed448VerifyEquation
