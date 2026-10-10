import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
import VerifiedGarbage.Proof.Weierstrass.Arm.MontP192

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for P-192's moduli,
in three 64-bit words. -/

namespace VG.Artifacts.WeierstrassMontP192.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  { p192p.mulApi with
    target := Arm.target
    doc := p192p.mulApi.doc (notes := notes)
    code := mulFn p192p.k p192p.m
    contract := p192p.mulContract Arm.abi
    verified := p192p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p192p.addApi with
    target := Arm.target
    doc := p192p.addApi.doc (notes := notes)
    code := addFn p192p.k p192p.m
    contract := p192p.addContract Arm.abi
    verified := p192p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p192p.subApi with
    target := Arm.target
    doc := p192p.subApi.doc (notes := notes)
    code := subFn p192p.k p192p.m
    contract := p192p.subContract Arm.abi
    verified := p192p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p192n.mulApi with
    target := Arm.target
    doc := p192n.mulApi.doc (notes := notes)
    code := mulFn p192n.k p192n.m
    contract := p192n.mulContract Arm.abi
    verified := p192n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p192n.addApi with
    target := Arm.target
    doc := p192n.addApi.doc (notes := notes)
    code := addFn p192n.k p192n.m
    contract := p192n.addContract Arm.abi
    verified := p192n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p192n.subApi with
    target := Arm.target
    doc := p192n.subApi.doc (notes := notes)
    code := subFn p192n.k p192n.m
    contract := p192n.subContract Arm.abi
    verified := p192n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.WeierstrassMontP192.Arm
