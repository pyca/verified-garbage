module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontP256Umaal
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontP224Umaal
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontP384Umaal
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo the curves' `p` and `n` on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

def artifacts : List Artifact := [
  p224p.mulApi.artifact Arm.target {
    code := mulFn p224p.k p224p.m
    verified := p224p_mul_verified },
  p224p.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU p224p.k p224p.m
    verified := p224p_mulU_verified
    features := ["umaal"] },
  p224p.addApi.artifact Arm.target {
    code := addFn p224p.k p224p.m
    verified := p224p_add_verified },
  p224p.subApi.artifact Arm.target {
    code := subFn p224p.k p224p.m
    verified := p224p_sub_verified },
  p224n.mulApi.artifact Arm.target {
    code := mulFn p224n.k p224n.m
    verified := p224n_mul_verified },
  p224n.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU p224n.k p224n.m
    verified := p224n_mulU_verified
    features := ["umaal"] },
  p224n.addApi.artifact Arm.target {
    code := addFn p224n.k p224n.m
    verified := p224n_add_verified },
  p224n.subApi.artifact Arm.target {
    code := subFn p224n.k p224n.m
    verified := p224n_sub_verified },
  p256p.mulApi.artifact Arm.target {
    code := mulFn p256p.k p256p.m
    verified := p256p_mul_verified },
  p256p.addApi.artifact Arm.target {
    code := addFn p256p.k p256p.m
    verified := p256p_add_verified },
  p256p.subApi.artifact Arm.target {
    code := subFn p256p.k p256p.m
    verified := p256p_sub_verified },
  p256n.mulApi.artifact Arm.target {
    code := mulFn p256n.k p256n.m
    verified := p256n_mul_verified },
  p256p.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU p256p.k p256p.m
    verified := p256p_mulU_verified
    features := ["umaal"] },
  p256n.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU p256n.k p256n.m
    verified := p256n_mulU_verified
    features := ["umaal"] },
  p256n.addApi.artifact Arm.target {
    code := addFn p256n.k p256n.m
    verified := p256n_add_verified },
  p256n.subApi.artifact Arm.target {
    code := subFn p256n.k p256n.m
    verified := p256n_sub_verified },
  p384p.mulApi.artifact Arm.target {
    code := mulFn p384p.k p384p.m
    verified := p384p_mul_verified },
  p384p.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU p384p.k p384p.m
    verified := p384p_mulU_verified
    features := ["umaal"] },
  p384p.addApi.artifact Arm.target {
    code := addFn p384p.k p384p.m
    verified := p384p_add_verified },
  p384p.subApi.artifact Arm.target {
    code := subFn p384p.k p384p.m
    verified := p384p_sub_verified },
  p384n.mulApi.artifact Arm.target {
    code := mulFn p384n.k p384n.m
    verified := p384n_mul_verified },
  p384n.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := mulFnU p384n.k p384n.m
    verified := p384n_mulU_verified
    features := ["umaal"] },
  p384n.addApi.artifact Arm.target {
    code := addFn p384n.k p384n.m
    verified := p384n_add_verified },
  p384n.subApi.artifact Arm.target {
    code := subFn p384n.k p384n.m
    verified := p384n_sub_verified },
  p521p.mulApi.artifact Arm.target {
    code := mulFn p521p.k p521p.m
    verified := p521p_mul_verified },
  p521p.addApi.artifact Arm.target {
    code := addFn p521p.k p521p.m
    verified := p521p_add_verified },
  p521p.subApi.artifact Arm.target {
    code := subFn p521p.k p521p.m
    verified := p521p_sub_verified },
  p521n.mulApi.artifact Arm.target {
    code := mulFn p521n.k p521n.m
    verified := p521n_mul_verified },
  p521n.addApi.artifact Arm.target {
    code := addFn p521n.k p521n.m
    verified := p521n_add_verified },
  p521n.subApi.artifact Arm.target {
    code := subFn p521n.k p521n.m
    verified := p521n_sub_verified }]

end VG.Artifacts.WeierstrassMont.Arm
