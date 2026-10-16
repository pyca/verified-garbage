module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point doubling and affine addition, in radix `2^64`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519R64.AArch64

open VG.Spec.Ed25519.Point64 VG.Impl.Ed25519.AArch64.Point64 VG.Proof.Ed25519.AArch64.Point64

/-- How the functions work. -/
def notes (what : String) : List String := ["Uses baseline integer instructions, and AdvSIMD \
  moves to keep `x20` to `x24` in lanes of `v16` to `v18` while it runs. Runs " ++ what ++
  ", with the temporaries in slots 8–15: Ed25519's field operations on four 64-bit words, \
  multiplied by rows and folded with `2^256 = 38`."]

def artifacts : List Artifact := [
  doubleExtApi.artifact AArch64.target {
    notes := notes "RFC 8032's doubling formula (§5.1.4): four \
      squarings and four products"
    code := doubleFn
    verified := doubleFn_verified
    stack := 0 },
  addAffineExtApi.artifact AArch64.target {
    notes := notes "RFC 8032's complete addition formula of the point \
      in slots 4–6, with `Z₁ · 2Z₂ = Z₁ + Z₁`: seven products"
    code := affFn
    verified := affFn_verified
    stack := 0 }]

end VG.Artifacts.Ed25519R64.AArch64
