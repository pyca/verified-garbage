import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: contracts for Montgomery-scaled polynomial arithmetic

**Trusted.** These are separate primitives from `multiplyNTT` and `nttInv`:
with `R = 2^32 mod q`, products retain a factor of `R⁻¹` and the inverse
transform multiplies by `R`. A caller can accumulate products and take their
inverse transform without converting each product to the ordinary
representation. All stored coefficients are still reduced to `[0, q)`.

The underlying operations are FIPS 204 Algorithms 42, 44 and 45. The
Montgomery factors are an internal representation choice, not a change to
those algorithms or to the encoded keys and signatures. In particular,
`montgomeryMultiplyAddNTT h f g` adds a scaled product to `h`; it does not
scale `h` again. The caller is responsible for using a consistent scale for
every term in a sum or difference.

The new functions have distinct names and contracts. They are not variants
of the ordinary-representation functions, whose contracts are unchanged.
-/

namespace VG.Spec.MlDsa

/-- The Montgomery radix `2^32`, reduced modulo `q` (4193792). -/
def montgomeryR : Zq := Fin.ofNat q 4294967296

/-- `R⁻¹ mod q`: `4193792 * 8265825 mod 8380417 = 1`. -/
def montgomeryRInv : Zq := 8265825

/-- Algorithm 45's coefficientwise product, multiplied by `R⁻¹`. -/
def montgomeryMultiplyNTT (f g : Poly) : Poly :=
  (multiplyNTT f g).map (· * montgomeryRInv)

/-- Add `R⁻¹ * MultiplyNTT(f, g)` to `h`, without rescaling `h`. -/
def montgomeryMultiplyAddNTT (h f g : Poly) : Poly :=
  add h (montgomeryMultiplyNTT f g)

/-- Algorithm 42's inverse transform, multiplied coefficientwise by `R`. -/
def montgomeryNttInv (f : Poly) : Poly := (nttInv f).map (· * montgomeryR)

/-- Reduced inputs `f` and `g`; a reduced, Montgomery-scaled product in `h`.
The initial contents of `h` are unrestricted. -/
def montgomeryMulContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun _h f g m => Reduced m f ∧ Reduced m g)
    (post := fun h f g m m' _ => PolyIs m' h (montgomeryMultiplyNTT (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- Reduced inputs `h`, `f` and `g`; adds the scaled product to `h`, reduced. -/
def montgomeryMulAddContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun h f g m => Reduced m h ∧ Reduced m f ∧ Reduced m g)
    (post := fun h f g m m' _ =>
      PolyIs m' h (montgomeryMultiplyAddNTT (polyAt m h) (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- A reduced input, transformed in place to `R * NTT⁻¹(f)`, reduced. -/
def montgomeryNttInvContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlaceContract A montgomeryNttInv stack

/-- A distinct API: its result is not the ordinary coefficientwise product. -/
def montgomeryMulApi : Api where
  module := "mldsa"
  name := "vg_mldsa_montgomery_multiply_ntt"
  sig := mulSig
  writeArgs := true
  contracts := some fun A stack => montgomeryMulContract A stack
  summary := "Writes `R^-1 * MultiplyNTT(*f, *g)` to `*h`, coefficientwise modulo \
    `q` = 8380417, reduced, where `R = 2^32 mod q`. The factor of `R^-1` is canceled by \
    `vg_mldsa_montgomery_inv_ntt`." ++ ctDoc "montgomeryMulContract"
  safety := [reducedSafety "f", reducedSafety "g"]

/-- Accumulates a scaled product without rescaling the accumulator. -/
def montgomeryMulAddApi : Api where
  module := "mldsa"
  name := "vg_mldsa_montgomery_multiply_add_ntt"
  sig := mulSig
  writeArgs := true
  contracts := some fun A stack => montgomeryMulAddContract A stack
  summary := "Adds `R^-1 * MultiplyNTT(*f, *g)` to `*h`, coefficientwise modulo \
    `q` = 8380417, reduced, where `R = 2^32 mod q`. The existing accumulator is not \
    rescaled; callers must keep every accumulated term at the same scale." ++
    ctDoc "montgomeryMulAddContract"
  safety := [reducedSafety "h", reducedSafety "f", reducedSafety "g"]

/-- An inverse transform that cancels the products' Montgomery factor. -/
def montgomeryNttInvApi : Api where
  module := "mldsa"
  name := "vg_mldsa_montgomery_inv_ntt"
  sig := inPlaceSig
  writeArgs := true
  contracts := some fun A stack => montgomeryNttInvContract A stack
  summary := "Replaces `*f` with `R * NTT^-1(*f)`, coefficientwise modulo \
    `q` = 8380417, reduced, where `R = 2^32 mod q`. An input scaled by `R^-1` produces \
    the ordinary inverse transform of the unscaled polynomial." ++ ctDoc "montgomeryNttInvContract"
  safety := [reducedSafety "f",
    "`scratch` is working space: on return it may hold intermediate values, which the caller \
      must destroy (FIPS 204 section 3.6.3)."]

end VG.Spec.MlDsa
