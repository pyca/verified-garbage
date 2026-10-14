module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
import Batteries.Logic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Taint

/-! # Montgomery arithmetic modulo brainpoolP512r1's `p` and `n` on ARMv7

The functions of `Artifacts/WeierstrassMont/Arm.lean` for brainpoolP512r1's moduli,
in eight 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.Arm

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.Arm.Mont VG.Proof.Weierstrass.Arm.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `r4`–`r11` in its own working space, stores the \
  modulus there, and reads `[a]` and `[b]` and writes `[o]` through pointers. The numbers are \
  16-bit digits, each in a word: the product is digit-by-digit Montgomery multiplication (CIOS, \
  with `mul` and the accumulator in the own working space), and every result is reduced by a \
  conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  { brainpoolp512r1p.mulApi with
    target := Arm.target
    doc := brainpoolp512r1p.mulApi.doc (notes := notes)
    code := mulFn brainpoolp512r1p.k brainpoolp512r1p.m
    contract := brainpoolp512r1p.mulContract Arm.abi
    verified := brainpoolp512r1p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { brainpoolp512r1p.addApi with
    target := Arm.target
    doc := brainpoolp512r1p.addApi.doc (notes := notes)
    code := addFn brainpoolp512r1p.k brainpoolp512r1p.m
    contract := brainpoolp512r1p.addContract Arm.abi
    verified := brainpoolp512r1p_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { brainpoolp512r1p.subApi with
    target := Arm.target
    doc := brainpoolp512r1p.subApi.doc (notes := notes)
    code := subFn brainpoolp512r1p.k brainpoolp512r1p.m
    contract := brainpoolp512r1p.subContract Arm.abi
    verified := brainpoolp512r1p_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { brainpoolp512r1n.mulApi with
    target := Arm.target
    doc := brainpoolp512r1n.mulApi.doc (notes := notes)
    code := mulFn brainpoolp512r1n.k brainpoolp512r1n.m
    contract := brainpoolp512r1n.mulContract Arm.abi
    verified := brainpoolp512r1n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { brainpoolp512r1n.addApi with
    target := Arm.target
    doc := brainpoolp512r1n.addApi.doc (notes := notes)
    code := addFn brainpoolp512r1n.k brainpoolp512r1n.m
    contract := brainpoolp512r1n.addContract Arm.abi
    verified := brainpoolp512r1n_add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { brainpoolp512r1n.subApi with
    target := Arm.target
    doc := brainpoolp512r1n.subApi.doc (notes := notes)
    code := subFn brainpoolp512r1n.k brainpoolp512r1n.m
    contract := brainpoolp512r1n.subContract Arm.abi
    verified := brainpoolp512r1n_sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.Arm
