import VerifiedGarbage.Spec.MlDsa.Montgomery

/-!
# Algebraic consistency checks for ML-DSA's Montgomery contracts

These synthetic polynomials exercise representation identities, not new
known-answer vectors. The existing NIST ACVP tests validate the underlying
FIPS 204 specification. Check products, accumulation, differences and the
inverse transform together to detect a missing or duplicated scale factor.
-/

namespace VG.Test.MlDsaMontgomery

open Spec.MlDsa

example : montgomeryR * montgomeryRInv = 1 := by decide +kernel

private def patterns : List Poly :=
  [Vector.replicate n 0, Vector.replicate n 1, Vector.replicate n (-1),
    Vector.ofFn (fun i => if i.val = 0 then 1 else 0),
    Vector.ofFn (fun i => if i.val = 255 then -1 else 0),
    Vector.ofFn (fun i => Fin.ofNat q (i.val * 32749 + 17))]

#eval show IO Unit from do
  for f in patterns do
    let scaled : Poly := Vector.map (fun x : Zq => x * montgomeryRInv) f
    unless scaled.map (· * montgomeryR) == f do
      throw (IO.userError "Montgomery scale round trip")
    unless montgomeryNttInv scaled == nttInv f do
      throw (IO.userError "Montgomery inverse-transform scale")
    for g in patterns do
      let product := montgomeryMultiplyNTT f g
      unless product.map (· * montgomeryR) == multiplyNTT f g do
        throw (IO.userError "Montgomery product scale")
      unless montgomeryNttInv product == nttInv (multiplyNTT f g) do
        throw (IO.userError "Montgomery product/inverse-transform composition")
      unless montgomeryMultiplyAddNTT scaled f g ==
          (add f (multiplyNTT f g)).map (· * montgomeryRInv) do
        throw (IO.userError "Montgomery accumulator scale")
      unless montgomeryNttInv (sub product scaled) == nttInv (sub (multiplyNTT f g) f) do
        throw (IO.userError "Montgomery difference/inverse-transform composition")

end VG.Test.MlDsaMontgomery
