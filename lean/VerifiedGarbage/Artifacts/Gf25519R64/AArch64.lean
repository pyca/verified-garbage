module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Pow250Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Powers in curve25519's field, in radix `2^64`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Gf25519R64.AArch64

open VG.Spec.X25519.Field64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Pow250

def artifacts : List Artifact := [
  pow250Api.artifact AArch64.target {
    notes := ["Uses baseline integer instructions, and AdvSIMD moves to keep \
      `x19` to `x24` in lanes of `v16` to `v18` while it runs. The addition chain of \
      `vg_x25519`'s inversion up to `a^(2^250 - 1)`, with Ed25519's field products (four 64-bit \
      words), the runs of squarings in loops counted by `x19`."]
    code := powFn
    verified := powFn_verified
    stack := 0 }]

end VG.Artifacts.Gf25519R64.AArch64
