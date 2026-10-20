module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Fns
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point doubling and cached additions, in radix `2^64`, on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519R64.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64.Point64
open VG.Impl.X25519.X86_64 (baseline adx)
open VG.Spec.Ed25519.Point64 (doubleExtApi addCachedExtApi addCachedProjApi addAffineExtApi doubleContract
  addCachedContract addAffineContract)

/-- How the functions work, with the field multiplications described by `mul`. -/
def notes (what mul : String) : List String := ["The function keeps `rbp` and `r12`–`r15` in `xmm0`–`xmm4` \
  while it runs, and runs " ++ what ++ " as `vg_ed25519_verify_equation` inlined it, with the \
  temporaries in slots 8–15: X25519's field operations on four 64-bit words, " ++ mul ++ ", folded \
  with `2^256 = 38`, and additions and subtractions, each folded once where an operand is a product."]

/-- The baseline's multiplications. -/
def baseMul : String := "multiplied with `mul` by rows (squares computing each cross product once)"

/-- BMI2 and ADX's multiplications. -/
def adxMul : String := "multiplied with BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once)"

/-- What the doubling runs. -/
def dblWhat : String :=
  "RFC 8032's doubling formula (§5.1.4), with `-E = 2XY` from one product and `F`, `G` and `H` \
    negated: eight products"

/-- What the additions run. -/
def addWhat (t : Bool) : String :=
  "RFC 8032's complete addition formula of the point in slots 4–7, cached, " ++
    (if t then "eight products" else "seven products, leaving out `T`'s")

/-- What the affine addition runs. -/
def affWhat : String :=
  "RFC 8032's complete addition formula of the point in slots 4–6, affine and cached, its `2Z` \
    `2` (so that `Z₁ · 2Z₂ = Z₁ + Z₁`): seven products"

/-- The affine addition's notes: `notes`, for the code of the comb's additions. -/
def affNotes (mul : String) : List String := ["The function keeps `rbp` and `r12`–`r15` in \
  `xmm0`–`xmm4` while it runs, and runs " ++ affWhat ++ ", as `vg_ed25519_scalar_base`'s comb \
  adds its table entries, with the temporaries in slots 8–15: X25519's field operations on four \
  64-bit words, " ++ mul ++ ", folded with `2^256 = 38`, and additions and subtractions, each \
  folded once where an operand is a product."]

def artifacts : List Artifact := [
  doubleExtApi.artifact X86_64.target {
    notes := (notes dblWhat baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·)
    code := doubleFn baseline true
    verified := doubleExt_verified },
  addCachedExtApi.artifact X86_64.target {
    notes := (notes (addWhat true) baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·)
    code := addFn baseline true
    verified := addExt_verified },
  addCachedProjApi.artifact X86_64.target {
    notes := (notes (addWhat false) baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·)
    code := addFn baseline false
    verified := addProj_verified },
  doubleExtApi.artifact X86_64.target {
    suffix := "_adx"
    notes := (notes dblWhat adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·)
    code := doubleFn adx true
    verified := doubleExtAdx_verified
    features := ["bmi2", "adx"] },
  addCachedExtApi.artifact X86_64.target {
    suffix := "_adx"
    notes := (notes (addWhat true) adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·)
    code := addFn adx true
    verified := addExtAdx_verified
    features := ["bmi2", "adx"] },
  addCachedProjApi.artifact X86_64.target {
    suffix := "_adx"
    notes := (notes (addWhat false) adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·)
    code := addFn adx false
    verified := addProjAdx_verified
    features := ["bmi2", "adx"] },
  addAffineExtApi.artifact X86_64.target {
    notes := (affNotes baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·)
    code := addAffineFn baseline
    verified := addAffine_verified },
  addAffineExtApi.artifact X86_64.target {
    suffix := "_adx"
    notes := (affNotes adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·)
    code := addAffineFn adx
    verified := addAffineAdx_verified
    features := ["bmi2", "adx"] }]

end VG.Artifacts.Ed25519R64.X86_64
