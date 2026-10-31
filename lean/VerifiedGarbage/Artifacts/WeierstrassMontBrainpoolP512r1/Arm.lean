module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1Umaal
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP512r1's `p` and `n` on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

def artifacts : List Artifact := [
  brainpoolp512r1p.mulApi.artifact Arm.target {
    code := mulFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_mul_verified },
  brainpoolp512r1p.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_mulU_verified
    features := ["umaal"] },
  brainpoolp512r1p.addApi.artifact Arm.target {
    code := addFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_add_verified },
  brainpoolp512r1p.subApi.artifact Arm.target {
    code := subFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_sub_verified },
  brainpoolp512r1n.mulApi.artifact Arm.target {
    code := mulFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_mul_verified },
  brainpoolp512r1n.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_mulU_verified
    features := ["umaal"] },
  brainpoolp512r1n.addApi.artifact Arm.target {
    code := addFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_add_verified },
  brainpoolp512r1n.subApi.artifact Arm.target {
    code := subFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.Arm
