module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontP192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for P-192's moduli,
in three 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontP192.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  p192p.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn p192p.k p192p.m
    verified := p192p_mul_verified },
  p192p.addApi.artifact Arm.target {
    notes := notes
    code := addFn p192p.k p192p.m
    verified := p192p_add_verified },
  p192p.subApi.artifact Arm.target {
    notes := notes
    code := subFn p192p.k p192p.m
    verified := p192p_sub_verified },
  p192n.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn p192n.k p192n.m
    verified := p192n_mul_verified },
  p192n.addApi.artifact Arm.target {
    notes := notes
    code := addFn p192n.k p192n.m
    verified := p192n_add_verified },
  p192n.subApi.artifact Arm.target {
    notes := notes
    code := subFn p192n.k p192n.m
    verified := p192n_sub_verified }]

end VG.Artifacts.WeierstrassMontP192.Arm
