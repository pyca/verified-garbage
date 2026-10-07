import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified

/-! # Montgomery arithmetic modulo the curves' `p` and `n` on ARMv7 -/

namespace VG.Artifacts.WeierstrassMont.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  { p224p.mulApi with
    target := Arm.target
    doc := p224p.mulApi.doc (notes := notes)
    code := mulFn p224p.k p224p.m
    contract := p224p.mulContract Arm.abi
    verified := p224p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p224p.addApi with
    target := Arm.target
    doc := p224p.addApi.doc (notes := notes)
    code := addFn p224p.k p224p.m
    contract := p224p.addContract Arm.abi
    verified := p224p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p224p.subApi with
    target := Arm.target
    doc := p224p.subApi.doc (notes := notes)
    code := subFn p224p.k p224p.m
    contract := p224p.subContract Arm.abi
    verified := p224p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p224n.mulApi with
    target := Arm.target
    doc := p224n.mulApi.doc (notes := notes)
    code := mulFn p224n.k p224n.m
    contract := p224n.mulContract Arm.abi
    verified := p224n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p224n.addApi with
    target := Arm.target
    doc := p224n.addApi.doc (notes := notes)
    code := addFn p224n.k p224n.m
    contract := p224n.addContract Arm.abi
    verified := p224n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p224n.subApi with
    target := Arm.target
    doc := p224n.subApi.doc (notes := notes)
    code := subFn p224n.k p224n.m
    contract := p224n.subContract Arm.abi
    verified := p224n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p256p.mulApi with
    target := Arm.target
    doc := p256p.mulApi.doc (notes := notes)
    code := mulFn p256p.k p256p.m
    contract := p256p.mulContract Arm.abi
    verified := p256p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p256p.addApi with
    target := Arm.target
    doc := p256p.addApi.doc (notes := notes)
    code := addFn p256p.k p256p.m
    contract := p256p.addContract Arm.abi
    verified := p256p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p256p.subApi with
    target := Arm.target
    doc := p256p.subApi.doc (notes := notes)
    code := subFn p256p.k p256p.m
    contract := p256p.subContract Arm.abi
    verified := p256p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p256n.mulApi with
    target := Arm.target
    doc := p256n.mulApi.doc (notes := notes)
    code := mulFn p256n.k p256n.m
    contract := p256n.mulContract Arm.abi
    verified := p256n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p256n.addApi with
    target := Arm.target
    doc := p256n.addApi.doc (notes := notes)
    code := addFn p256n.k p256n.m
    contract := p256n.addContract Arm.abi
    verified := p256n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p256n.subApi with
    target := Arm.target
    doc := p256n.subApi.doc (notes := notes)
    code := subFn p256n.k p256n.m
    contract := p256n.subContract Arm.abi
    verified := p256n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384p.mulApi with
    target := Arm.target
    doc := p384p.mulApi.doc (notes := notes)
    code := mulFn p384p.k p384p.m
    contract := p384p.mulContract Arm.abi
    verified := p384p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384p.addApi with
    target := Arm.target
    doc := p384p.addApi.doc (notes := notes)
    code := addFn p384p.k p384p.m
    contract := p384p.addContract Arm.abi
    verified := p384p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384p.subApi with
    target := Arm.target
    doc := p384p.subApi.doc (notes := notes)
    code := subFn p384p.k p384p.m
    contract := p384p.subContract Arm.abi
    verified := p384p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384n.mulApi with
    target := Arm.target
    doc := p384n.mulApi.doc (notes := notes)
    code := mulFn p384n.k p384n.m
    contract := p384n.mulContract Arm.abi
    verified := p384n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384n.addApi with
    target := Arm.target
    doc := p384n.addApi.doc (notes := notes)
    code := addFn p384n.k p384n.m
    contract := p384n.addContract Arm.abi
    verified := p384n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384n.subApi with
    target := Arm.target
    doc := p384n.subApi.doc (notes := notes)
    code := subFn p384n.k p384n.m
    contract := p384n.subContract Arm.abi
    verified := p384n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521p.mulApi with
    target := Arm.target
    doc := p521p.mulApi.doc (notes := notes)
    code := mulFn p521p.k p521p.m
    contract := p521p.mulContract Arm.abi
    verified := p521p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521p.addApi with
    target := Arm.target
    doc := p521p.addApi.doc (notes := notes)
    code := addFn p521p.k p521p.m
    contract := p521p.addContract Arm.abi
    verified := p521p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521p.subApi with
    target := Arm.target
    doc := p521p.subApi.doc (notes := notes)
    code := subFn p521p.k p521p.m
    contract := p521p.subContract Arm.abi
    verified := p521p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521n.mulApi with
    target := Arm.target
    doc := p521n.mulApi.doc (notes := notes)
    code := mulFn p521n.k p521n.m
    contract := p521n.mulContract Arm.abi
    verified := p521n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521n.addApi with
    target := Arm.target
    doc := p521n.addApi.doc (notes := notes)
    code := addFn p521n.k p521n.m
    contract := p521n.addContract Arm.abi
    verified := p521n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521n.subApi with
    target := Arm.target
    doc := p521n.subApi.doc (notes := notes)
    code := subFn p521n.k p521n.m
    contract := p521n.subContract Arm.abi
    verified := p521n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.WeierstrassMont.Arm
