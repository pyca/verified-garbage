module

public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA: the contracts of Montgomery-scaled polynomial arithmetic

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

These are separate functions from `multiplyNTT` and `nttInv`: with
`R = 2^32 mod q`, products retain a factor of `R⁻¹` and the inverse
transform multiplies by `R`. A caller can accumulate products and take their
inverse transform without converting each product to the ordinary
representation. All stored coefficients are still reduced to `[0, q)`.

The underlying operations are FIPS 204 Algorithms 42, 44 and 45. The
Montgomery factors are an internal representation choice, not a change to
those algorithms or to the encoded keys and signatures. In particular,
`montgomeryMultiplyAddNTT h f g` adds a scaled product to `h`; it does not
scale `h` again. The caller is responsible for using a consistent scale for
every term in a sum or difference.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

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

end VG.Proof.MlDsa
