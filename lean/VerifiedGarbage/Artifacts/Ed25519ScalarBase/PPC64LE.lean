module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBaseVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `[s] B`, encoded, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions and a fixed schedule for all 256 input bits, \
      ARMv7's: the powers `[2^(16 j)] B` into a table, then for each 16-bit batch from the top, \
      its powers `[2^i] Q` of its checkpoint, each added to the accumulator and the sum kept or \
      discarded by the bit with a mask. Point additions and doublings are calls of \
      `vg_ed25519_r32_point_add`, field products calls of `vg_gf25519_r32_mul`, and the \
      inversion's chain to `z^(2^250 - 1)` a call of `vg_gf25519_r32_pow250`, each on `scratch`. \
      Point tables, the saved nonvolatile registers and `lr` reside in `scratch`."]
    code := Impl.Ed25519.PPC64LE.scalarBase
    verified := Proof.Ed25519.PPC64LE.scalarBase_verified }]

end VG.Artifacts.Ed25519ScalarBase.PPC64LE
