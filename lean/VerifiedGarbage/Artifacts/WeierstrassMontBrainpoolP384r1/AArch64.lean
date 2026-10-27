module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontBrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Shared BrainpoolP384r1 Montgomery products on AArch64 -/

@[expose] public section
namespace VG.Artifacts.WeierstrassMontBrainpoolP384r1.AArch64
open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

def artifacts : List Artifact := [
  brainpoolp384r1p.mulApi.artifact AArch64.target {
    code := mulFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_mul_verified },
  brainpoolp384r1n.mulApi.artifact AArch64.target {
    code := mulFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_mul_verified }
]

end VG.Artifacts.WeierstrassMontBrainpoolP384r1.AArch64
