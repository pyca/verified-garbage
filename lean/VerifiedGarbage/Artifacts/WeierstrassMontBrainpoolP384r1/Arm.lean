module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP384r1's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for brainpoolP384r1's moduli,
in six 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP384r1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

def artifacts : List Artifact := [
  brainpoolp384r1p.mulApi.artifact Arm.target {
    code := mulFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_mul_verified },
  brainpoolp384r1p.addApi.artifact Arm.target {
    code := addFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_add_verified },
  brainpoolp384r1p.subApi.artifact Arm.target {
    code := subFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_sub_verified },
  brainpoolp384r1n.mulApi.artifact Arm.target {
    code := mulFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_mul_verified },
  brainpoolp384r1n.addApi.artifact Arm.target {
    code := addFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_add_verified },
  brainpoolp384r1n.subApi.artifact Arm.target {
    code := subFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP384r1.Arm
