module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit

/-! # Ed448's point doubling and affine addition, in radix `2^64`, on x86-64 -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448R64

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448.X86_64.Point64
open VG.Spec.Ed448.Point64 (doubleApi addAffineApi doubleContract addAffineContract)

/-- How the functions work. -/
def notes (v : Impl.Ed448.X86_64.FieldVariant) (formula : String) : List String := ["Uses " ++ (match v with | .scalar => "baseline integer arithmetic" | .adx => "BMI2/ADX field multiplication") ++ ", and SSE2 moves \
  to keep `rbp` and `r12`–`r15` in `xmm0`–`xmm4` while it runs. " ++ formula ++ ", with \
  `vg_x448`'s field operations on seven 64-bit words (using the selected field multiplier), the \
  temporaries in slots 12 to 20 and the product's words at byte 1536."]

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  doubleApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := notes v "Runs RFC 8032's doubling formulas, seven products"
    code := v.doubleFn
    verified := Proof.Ed448.X86_64.FieldVariant.double_verified v },
  addAffineApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := notes v "Runs RFC 8032's complete addition formula with \
      `A = Z₁` for `Z₁ Z₂`, as `Z₂ = 1`: nine full products and multiplication by \
      `d = -39081` using negation and X448's small-constant multiplier"
    code := v.addFn
    verified := Proof.Ed448.X86_64.FieldVariant.add_verified v }]

end VG.Generic.Curve448Field.X86_64.Ed448R64
