module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo the curves' `p` and `n` on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

/-- The larger curves’ product scans packed words while retaining the curve ABI. -/
def packedNotes : List String := ["The function saves `r4`–`r9` and `lr` in its existing working \
  space. Montgomery multiplication scans packed 32-bit words, assembling each full \
  product from four baseline 16-by-16 `mul` products. Fixed-offset rows keep `r10` and `r11` \
  unchanged and `r12` as the workspace pointer. The accumulator is expanded to half-word \
  digits for the existing mask-selected final subtraction. No stack or CPU extension is used."]

def artifacts : List Artifact := [
  p224p.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn p224p.k p224p.m
    verified := p224p_mul_verified },
  p224p.addApi.artifact Arm.target {
    notes := notes
    code := addFn p224p.k p224p.m
    verified := p224p_add_verified },
  p224p.subApi.artifact Arm.target {
    notes := notes
    code := subFn p224p.k p224p.m
    verified := p224p_sub_verified },
  p224n.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn p224n.k p224n.m
    verified := p224n_mul_verified },
  p224n.addApi.artifact Arm.target {
    notes := notes
    code := addFn p224n.k p224n.m
    verified := p224n_add_verified },
  p224n.subApi.artifact Arm.target {
    notes := notes
    code := subFn p224n.k p224n.m
    verified := p224n_sub_verified },
  p256p.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn p256p.k p256p.m
    verified := p256p_mul_verified },
  p256p.addApi.artifact Arm.target {
    notes := notes
    code := addFn p256p.k p256p.m
    verified := p256p_add_verified },
  p256p.subApi.artifact Arm.target {
    notes := notes
    code := subFn p256p.k p256p.m
    verified := p256p_sub_verified },
  p256n.mulApi.artifact Arm.target {
    notes := notes
    code := mulFn p256n.k p256n.m
    verified := p256n_mul_verified },
  p256n.addApi.artifact Arm.target {
    notes := notes
    code := addFn p256n.k p256n.m
    verified := p256n_add_verified },
  p256n.subApi.artifact Arm.target {
    notes := notes
    code := subFn p256n.k p256n.m
    verified := p256n_sub_verified },
  p384p.mulApi.artifact Arm.target {
    notes := packedNotes
    code := mulFn p384p.k p384p.m
    verified := p384p_mul_verified },
  p384p.addApi.artifact Arm.target {
    notes := notes
    code := addFn p384p.k p384p.m
    verified := p384p_add_verified },
  p384p.subApi.artifact Arm.target {
    notes := notes
    code := subFn p384p.k p384p.m
    verified := p384p_sub_verified },
  p384n.mulApi.artifact Arm.target {
    notes := packedNotes
    code := mulFn p384n.k p384n.m
    verified := p384n_mul_verified },
  p384n.addApi.artifact Arm.target {
    notes := notes
    code := addFn p384n.k p384n.m
    verified := p384n_add_verified },
  p384n.subApi.artifact Arm.target {
    notes := notes
    code := subFn p384n.k p384n.m
    verified := p384n_sub_verified },
  p521p.mulApi.artifact Arm.target {
    notes := packedNotes
    code := mulFn p521p.k p521p.m
    verified := p521p_mul_verified },
  p521p.addApi.artifact Arm.target {
    notes := notes
    code := addFn p521p.k p521p.m
    verified := p521p_add_verified },
  p521p.subApi.artifact Arm.target {
    notes := notes
    code := subFn p521p.k p521p.m
    verified := p521p_sub_verified },
  p521n.mulApi.artifact Arm.target {
    notes := packedNotes
    code := mulFn p521n.k p521n.m
    verified := p521n_mul_verified },
  p521n.addApi.artifact Arm.target {
    notes := notes
    code := addFn p521n.k p521n.m
    verified := p521n_add_verified },
  p521n.subApi.artifact Arm.target {
    notes := notes
    code := subFn p521n.k p521n.m
    verified := p521n_sub_verified }]

end VG.Artifacts.WeierstrassMont.Arm
