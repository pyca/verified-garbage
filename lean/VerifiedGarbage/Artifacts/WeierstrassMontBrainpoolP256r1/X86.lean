module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1

/-! # Montgomery arithmetic modulo brainpoolP256r1's `p` and `n` on x86 (32-bit)

The functions of `Artifacts/WeierstrassMont/X86.lean` for brainpoolP256r1's moduli,
in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP256r1.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

def artifacts : List Artifact := [
  brainpoolp256r1p.mulApi.artifact X86.target {
    code := mulFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_mul_verified },
  brainpoolp256r1p.addApi.artifact X86.target {
    code := addFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_add_verified },
  brainpoolp256r1p.subApi.artifact X86.target {
    code := subFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_sub_verified },
  brainpoolp256r1n.mulApi.artifact X86.target {
    code := mulFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_mul_verified },
  brainpoolp256r1n.addApi.artifact X86.target {
    code := addFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_add_verified },
  brainpoolp256r1n.subApi.artifact X86.target {
    code := subFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP256r1.X86
