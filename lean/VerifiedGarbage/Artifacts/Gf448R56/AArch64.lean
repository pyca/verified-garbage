module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulVerified

/-! # A power and the product in curve448's field, in radix `2^56`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Gf448R56.AArch64

open VG.Spec.X448.Field56 VG.Impl.Ed448.AArch64.Point56 VG.Proof.Ed448.AArch64.Point56

def artifacts : List Artifact := [
  { powApi with
    target := AArch64.target
    doc := powApi.doc (notes := ["Uses baseline integer instructions, and AdvSIMD moves to keep \
      `x19`, `x21` to `x28` and `x30` in lanes of `v16` to `v20` while it runs. Runs X448's \
      inversion chain up to `a^(2^223 - 1)`, then 223 squarings and a product, with `vg_x448`'s \
      field squarings (eight 56-bit limbs in 64-bit words), in loops counted by `x19`, and its \
      products as calls of `vg_gf448_r56_mul`."])
    code := powFn
    contract := powContract AArch64.abi
    verified := powFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { mulApi with
    target := AArch64.target
    doc := mulApi.doc (notes := ["Uses baseline integer instructions, and AdvSIMD moves to keep \
      `x30` and `x21` to `x28` in lanes of `v21` to `v25` while it runs; it writes neither `x19` \
      nor `x20`. `vg_x448`'s field product (eight 56-bit limbs in 64-bit words, Karatsuba's \
      identity for the halves) with its operands addressed by `ws` plus their offsets. \
      `vg_gf448_r56_pow_p34`, `vg_x448`, `vg_x448_base`, `vg_ed448_scalar_base` and \
      `vg_ed448_verify_equation` call it for their products of distinct operands outside loops."])
    code := mulFn
    contract := mulContract AArch64.abi
    verified := mulFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gf448R56.AArch64
