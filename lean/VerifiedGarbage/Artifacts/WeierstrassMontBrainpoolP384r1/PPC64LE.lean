module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontBrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP384r1's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for brainpoolP384r1's moduli, in six 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP384r1.PPC64LE

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Mont

def artifacts : List Artifact := [
  brainpoolp384r1p.mulApi.artifact PPC64LE.target {
    code := mulFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_mul_verified },
  brainpoolp384r1p.addApi.artifact PPC64LE.target {
    code := addFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_add_verified },
  brainpoolp384r1p.subApi.artifact PPC64LE.target {
    code := subFn brainpoolp384r1p.k brainpoolp384r1p.m
    verified := brainpoolp384r1p_sub_verified },
  brainpoolp384r1n.mulApi.artifact PPC64LE.target {
    code := mulFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_mul_verified },
  brainpoolp384r1n.addApi.artifact PPC64LE.target {
    code := addFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_add_verified },
  brainpoolp384r1n.subApi.artifact PPC64LE.target {
    code := subFn brainpoolp384r1n.k brainpoolp384r1n.m
    verified := brainpoolp384r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP384r1.PPC64LE
