module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP512r1's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for brainpoolP512r1's moduli,
in eight 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  brainpoolp512r1p.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_mul_verified },
  brainpoolp512r1p.addApi.artifact Arm.target {
    notes := notes
    code := addFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_add_verified },
  brainpoolp512r1p.subApi.artifact Arm.target {
    notes := notes
    code := subFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_sub_verified },
  brainpoolp512r1n.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_mul_verified },
  brainpoolp512r1n.addApi.artifact Arm.target {
    notes := notes
    code := addFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_add_verified },
  brainpoolp512r1n.subApi.artifact Arm.target {
    notes := notes
    code := subFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.Arm
