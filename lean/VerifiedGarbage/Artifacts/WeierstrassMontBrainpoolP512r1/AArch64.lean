module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontBrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Shared BrainpoolP512r1 Montgomery products on AArch64 -/

@[expose] public section
namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.AArch64
open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

def artifacts : List Artifact := [
  brainpoolp512r1p.mulApi.artifact AArch64.target {
    code := mulFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_mul_verified },
  brainpoolp512r1n.mulApi.artifact AArch64.target {
    code := mulFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_mul_verified }
]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.AArch64
