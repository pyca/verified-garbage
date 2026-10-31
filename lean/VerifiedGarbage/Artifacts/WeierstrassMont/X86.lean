module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521

/-! # Montgomery arithmetic modulo the curves' `p` and `n` on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

def artifacts : List Artifact := [
  p224p.mulApi.artifact X86.target {
    code := mulFn p224p.k p224p.m
    verified := p224p_mul_verified },
  p224p.addApi.artifact X86.target {
    code := addFn p224p.k p224p.m
    verified := p224p_add_verified },
  p224p.subApi.artifact X86.target {
    code := subFn p224p.k p224p.m
    verified := p224p_sub_verified },
  p224n.mulApi.artifact X86.target {
    code := mulFn p224n.k p224n.m
    verified := p224n_mul_verified },
  p224n.addApi.artifact X86.target {
    code := addFn p224n.k p224n.m
    verified := p224n_add_verified },
  p224n.subApi.artifact X86.target {
    code := subFn p224n.k p224n.m
    verified := p224n_sub_verified },
  p256p.mulApi.artifact X86.target {
    code := mulFn p256p.k p256p.m
    verified := p256p_mul_verified },
  p256p.addApi.artifact X86.target {
    code := addFn p256p.k p256p.m
    verified := p256p_add_verified },
  p256p.subApi.artifact X86.target {
    code := subFn p256p.k p256p.m
    verified := p256p_sub_verified },
  p256n.mulApi.artifact X86.target {
    code := mulFn p256n.k p256n.m
    verified := p256n_mul_verified },
  p256n.addApi.artifact X86.target {
    code := addFn p256n.k p256n.m
    verified := p256n_add_verified },
  p384p.mulApi.artifact X86.target {
    code := mulFn p384p.k p384p.m
    verified := p384p_mul_verified },
  p384p.addApi.artifact X86.target {
    code := addFn p384p.k p384p.m
    verified := p384p_add_verified },
  p384p.subApi.artifact X86.target {
    code := subFn p384p.k p384p.m
    verified := p384p_sub_verified },
  p384n.mulApi.artifact X86.target {
    code := mulFn p384n.k p384n.m
    verified := p384n_mul_verified },
  p384n.addApi.artifact X86.target {
    code := addFn p384n.k p384n.m
    verified := p384n_add_verified },
  p384n.subApi.artifact X86.target {
    code := subFn p384n.k p384n.m
    verified := p384n_sub_verified },
  p521p.mulApi.artifact X86.target {
    code := mulFn p521p.k p521p.m
    verified := p521p_mul_verified },
  p521p.addApi.artifact X86.target {
    code := addFn p521p.k p521p.m
    verified := p521p_add_verified },
  p521p.subApi.artifact X86.target {
    code := subFn p521p.k p521p.m
    verified := p521p_sub_verified },
  p521n.mulApi.artifact X86.target {
    code := mulFn p521n.k p521n.m
    verified := p521n_mul_verified },
  p521n.addApi.artifact X86.target {
    code := addFn p521n.k p521n.m
    verified := p521n_add_verified },
  p521n.subApi.artifact X86.target {
    code := subFn p521n.k p521n.m
    verified := p521n_sub_verified }]

end VG.Artifacts.WeierstrassMont.X86
