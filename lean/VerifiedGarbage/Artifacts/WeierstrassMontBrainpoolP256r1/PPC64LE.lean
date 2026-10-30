module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP256r1's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for brainpoolP256r1's moduli, in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP256r1.PPC64LE

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Mont

def artifacts : List Artifact := [
  brainpoolp256r1p.mulApi.artifact PPC64LE.target {
    code := mulFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_mul_verified },
  brainpoolp256r1p.addApi.artifact PPC64LE.target {
    code := addFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_add_verified },
  brainpoolp256r1p.subApi.artifact PPC64LE.target {
    code := subFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_sub_verified },
  brainpoolp256r1n.mulApi.artifact PPC64LE.target {
    code := mulFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_mul_verified },
  brainpoolp256r1n.addApi.artifact PPC64LE.target {
    code := addFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_add_verified },
  brainpoolp256r1n.subApi.artifact PPC64LE.target {
    code := subFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP256r1.PPC64LE
