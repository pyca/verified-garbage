module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
import Batteries.Logic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519

/-! # Montgomery arithmetic modulo secp256k1's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for secp256k1's moduli,
in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontSecp256k1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  { secp256k1p.mulApi with
    target := Arm.target
    doc := secp256k1p.mulApi.doc (notes := notes)
    code := mulFn secp256k1p.k secp256k1p.m
    contract := secp256k1p.mulContract Arm.abi
    verified := secp256k1p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { secp256k1p.addApi with
    target := Arm.target
    doc := secp256k1p.addApi.doc (notes := notes)
    code := addFn secp256k1p.k secp256k1p.m
    contract := secp256k1p.addContract Arm.abi
    verified := secp256k1p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { secp256k1p.subApi with
    target := Arm.target
    doc := secp256k1p.subApi.doc (notes := notes)
    code := subFn secp256k1p.k secp256k1p.m
    contract := secp256k1p.subContract Arm.abi
    verified := secp256k1p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { secp256k1n.mulApi with
    target := Arm.target
    doc := secp256k1n.mulApi.doc (notes := notes)
    code := mulFn secp256k1n.k secp256k1n.m
    contract := secp256k1n.mulContract Arm.abi
    verified := secp256k1n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { secp256k1n.addApi with
    target := Arm.target
    doc := secp256k1n.addApi.doc (notes := notes)
    code := addFn secp256k1n.k secp256k1n.m
    contract := secp256k1n.addContract Arm.abi
    verified := secp256k1n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { secp256k1n.subApi with
    target := Arm.target
    doc := secp256k1n.subApi.doc (notes := notes)
    code := subFn secp256k1n.k secp256k1n.m
    contract := secp256k1n.subContract Arm.abi
    verified := secp256k1n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.WeierstrassMontSecp256k1.Arm
