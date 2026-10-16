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
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 base-point multiplication on x86-64

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448ScalarBase

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.scalarBaseApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := ["Expands all 456 scalar bits into bytes, \
      then uses a four-column comb with 114 rows and 16 precomputed affine points. Each row \
      doubles the accumulator and adds one point, selected by scanning the entire table \
      with constant-time masks. Point operations call `vg_ed448_r64_point_double` and \
      `vg_ed448_r64_point_add_affine`. Field elements use X448's seven 64-bit words. \
      The final inversion calls `vg_gf448_r64_pow223`. Callee-saved registers occupy the \
      first 48 bytes of scratch; the output address occupies the next 8."]
    code := Impl.Ed448.X86_64.scalarBaseFor v
    stack := 8
    verified := Proof.Ed448.X86_64.scalarBaseFor_verified v Proof.Ed448.baseLadder_ok }]

end VG.Generic.Curve448Field.X86_64.Ed448ScalarBase
