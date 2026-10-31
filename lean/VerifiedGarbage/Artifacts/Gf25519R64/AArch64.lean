module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Pow250Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Powers in curve25519's field, in radix `2^64`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Gf25519R64.AArch64

open VG.Spec.X25519.Field64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Pow250

def artifacts : List Artifact := [
  pow250Api.artifact AArch64.target {
    code := powFn
    verified := powFn_verified
    stack := 0 }]

end VG.Artifacts.Gf25519R64.AArch64
