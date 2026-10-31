module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontP192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for P-192's moduli, in three 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontP192.PPC64LE

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Mont

def artifacts : List Artifact := [
  p192p.mulApi.artifact PPC64LE.target {
    code := mulFn p192p.k p192p.m
    verified := p192p_mul_verified },
  p192p.addApi.artifact PPC64LE.target {
    code := addFn p192p.k p192p.m
    verified := p192p_add_verified },
  p192p.subApi.artifact PPC64LE.target {
    code := subFn p192p.k p192p.m
    verified := p192p_sub_verified },
  p192n.mulApi.artifact PPC64LE.target {
    code := mulFn p192n.k p192n.m
    verified := p192n_mul_verified },
  p192n.addApi.artifact PPC64LE.target {
    code := addFn p192n.k p192n.m
    verified := p192n_add_verified },
  p192n.subApi.artifact PPC64LE.target {
    code := subFn p192n.k p192n.m
    verified := p192n_sub_verified }]

end VG.Artifacts.WeierstrassMontP192.PPC64LE
