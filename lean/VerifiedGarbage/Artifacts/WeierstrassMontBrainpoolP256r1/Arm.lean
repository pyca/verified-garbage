module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP256r1's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for brainpoolP256r1's moduli,
in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP256r1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

def artifacts : List Artifact := [
  brainpoolp256r1p.mulApi.artifact Arm.target {
    code := mulFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_mul_verified },
  brainpoolp256r1p.addApi.artifact Arm.target {
    code := addFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_add_verified },
  brainpoolp256r1p.subApi.artifact Arm.target {
    code := subFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_sub_verified },
  brainpoolp256r1n.mulApi.artifact Arm.target {
    code := mulFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_mul_verified },
  brainpoolp256r1n.addApi.artifact Arm.target {
    code := addFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_add_verified },
  brainpoolp256r1n.subApi.artifact Arm.target {
    code := subFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP256r1.Arm
