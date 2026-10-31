module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point doubling and affine addition, in radix `2^64`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519R64.AArch64

open VG.Spec.Ed25519.Point64 VG.Impl.Ed25519.AArch64.Point64 VG.Proof.Ed25519.AArch64.Point64

def artifacts : List Artifact := [
  doubleExtApi.artifact AArch64.target {
    code := doubleFn
    verified := doubleFn_verified
    stack := 0 },
  addAffineExtApi.artifact AArch64.target {
    code := affFn
    verified := affFn_verified
    stack := 0 }]

end VG.Artifacts.Ed25519R64.AArch64
