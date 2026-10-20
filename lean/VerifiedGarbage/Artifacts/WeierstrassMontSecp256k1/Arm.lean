module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo secp256k1's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for secp256k1's moduli,
in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontSecp256k1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  secp256k1p.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_mul_verified },
  secp256k1p.addApi.artifact Arm.target {
    notes := notes
    code := addFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_add_verified },
  secp256k1p.subApi.artifact Arm.target {
    notes := notes
    code := subFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_sub_verified },
  secp256k1n.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_mul_verified },
  secp256k1n.addApi.artifact Arm.target {
    notes := notes
    code := addFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_add_verified },
  secp256k1n.subApi.artifact Arm.target {
    notes := notes
    code := subFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_sub_verified }]

end VG.Artifacts.WeierstrassMontSecp256k1.Arm
