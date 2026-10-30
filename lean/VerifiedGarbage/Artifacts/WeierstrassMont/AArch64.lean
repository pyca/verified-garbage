module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSqr521Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery products modulo the curves' `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.AArch64

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

def artifacts : List Artifact := [
  p384p.mulApi.artifact AArch64.target {
    code := mulFn p384p.k p384p.m
    verified := p384p_mul_verified },
  p384p.sqrApi.artifact AArch64.target {
    code := sqrFn384
    verified := p384p_sqr_verified },
  p521p.sqrApi.artifact AArch64.target {
    code := sqrFn521
    verified := p521p_sqr_verified },
  p521p.mulApi.artifact AArch64.target {
    code := mulFn p521p.k p521p.m
    verified := p521p_mul_verified },
  p384n.mulApi.artifact AArch64.target {
    code := mulFn p384n.k p384n.m
    verified := p384n_mul_verified },
  p521n.mulApi.artifact AArch64.target {
    code := mulFn p521n.k p521n.m
    verified := p521n_mul_verified }
]

end VG.Artifacts.WeierstrassMont.AArch64
