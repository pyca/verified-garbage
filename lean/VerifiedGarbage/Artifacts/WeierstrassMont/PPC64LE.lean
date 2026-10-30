module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontP224
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontP256
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontP384
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontP521
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo the curves' `p` and `n` on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.PPC64LE

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Mont

def artifacts : List Artifact := [
  p224p.mulApi.artifact PPC64LE.target {
    code := mulFn p224p.k p224p.m
    verified := p224p_mul_verified },
  p224p.addApi.artifact PPC64LE.target {
    code := addFn p224p.k p224p.m
    verified := p224p_add_verified },
  p224p.subApi.artifact PPC64LE.target {
    code := subFn p224p.k p224p.m
    verified := p224p_sub_verified },
  p224n.mulApi.artifact PPC64LE.target {
    code := mulFn p224n.k p224n.m
    verified := p224n_mul_verified },
  p224n.addApi.artifact PPC64LE.target {
    code := addFn p224n.k p224n.m
    verified := p224n_add_verified },
  p224n.subApi.artifact PPC64LE.target {
    code := subFn p224n.k p224n.m
    verified := p224n_sub_verified },
  p256p.mulApi.artifact PPC64LE.target {
    code := mulFn p256p.k p256p.m
    verified := p256p_mul_verified },
  p256p.addApi.artifact PPC64LE.target {
    code := addFn p256p.k p256p.m
    verified := p256p_add_verified },
  p256p.subApi.artifact PPC64LE.target {
    code := subFn p256p.k p256p.m
    verified := p256p_sub_verified },
  p256n.mulApi.artifact PPC64LE.target {
    code := mulFn p256n.k p256n.m
    verified := p256n_mul_verified },
  p256n.addApi.artifact PPC64LE.target {
    code := addFn p256n.k p256n.m
    verified := p256n_add_verified },
  p256n.subApi.artifact PPC64LE.target {
    code := subFn p256n.k p256n.m
    verified := p256n_sub_verified },
  p384p.mulApi.artifact PPC64LE.target {
    code := mulFn p384p.k p384p.m
    verified := p384p_mul_verified },
  p384p.addApi.artifact PPC64LE.target {
    code := addFn p384p.k p384p.m
    verified := p384p_add_verified },
  p384p.subApi.artifact PPC64LE.target {
    code := subFn p384p.k p384p.m
    verified := p384p_sub_verified },
  p384n.mulApi.artifact PPC64LE.target {
    code := mulFn p384n.k p384n.m
    verified := p384n_mul_verified },
  p384n.addApi.artifact PPC64LE.target {
    code := addFn p384n.k p384n.m
    verified := p384n_add_verified },
  p384n.subApi.artifact PPC64LE.target {
    code := subFn p384n.k p384n.m
    verified := p384n_sub_verified },
  p521p.mulApi.artifact PPC64LE.target {
    code := mulFn p521p.k p521p.m
    verified := p521p_mul_verified },
  p521p.addApi.artifact PPC64LE.target {
    code := addFn p521p.k p521p.m
    verified := p521p_add_verified },
  p521p.subApi.artifact PPC64LE.target {
    code := subFn p521p.k p521p.m
    verified := p521p_sub_verified },
  p521n.mulApi.artifact PPC64LE.target {
    code := mulFn p521n.k p521n.m
    verified := p521n_mul_verified },
  p521n.addApi.artifact PPC64LE.target {
    code := addFn p521n.k p521n.m
    verified := p521n_add_verified },
  p521n.subApi.artifact PPC64LE.target {
    code := subFn p521n.k p521n.m
    verified := p521n_sub_verified }]

end VG.Artifacts.WeierstrassMont.PPC64LE
