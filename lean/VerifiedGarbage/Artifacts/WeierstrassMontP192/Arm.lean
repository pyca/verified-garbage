module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontP192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontP192.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

def artifacts : List Artifact := [
  p192p.mulApi.artifact Arm.target {
    code := mulFn p192p.k p192p.m
    verified := p192p_mul_verified },
  p192p.addApi.artifact Arm.target {
    code := addFn p192p.k p192p.m
    verified := p192p_add_verified },
  p192p.subApi.artifact Arm.target {
    code := subFn p192p.k p192p.m
    verified := p192p_sub_verified },
  p192n.mulApi.artifact Arm.target {
    code := mulFn p192n.k p192n.m
    verified := p192n_mul_verified },
  p192n.addApi.artifact Arm.target {
    code := addFn p192n.k p192n.m
    verified := p192n_add_verified },
  p192n.subApi.artifact Arm.target {
    code := subFn p192n.k p192n.m
    verified := p192n_sub_verified }]

end VG.Artifacts.WeierstrassMontP192.Arm
