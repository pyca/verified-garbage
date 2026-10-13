module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Mont
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Spec.Ecdsa.Generic

/-! # Montgomery products modulo the curves' `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.AArch64

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

/-- How the functions work. -/
def notes : List String := ["The function zero-extends the offsets, saves the callee-saved \
  registers it writes in lanes of `v16`–`v20`, and keeps every word it multiplies by in a register: \
  all of `[b]`. The product is word-by-word Montgomery multiplication (CIOS, with `mul` and \
  `umulh`, the accumulator in registers, one word of `[a]` loaded per round), whose reductions \
  multiply by no word of the modulus: P-384's `p` is sparse (`u p` is `u (2^384 + 2^32)`, by \
  shifts, less `u (2^128 + 2^96 + 1)`, by a subtraction), P-521's reduced by shifts. A final \
  conditional subtraction against the modulus, built in registers (`movz`/`movk`), is selected by \
  `csel`."]

/-- How the functions for a general modulus work. -/
def notesG : List String := ["The function zero-extends the offsets, saves the callee-saved \
  registers it writes in lanes of `v16`–`v19`, writes the modulus's words (`movz`/`movk`) into its \
  own working space, and runs the inline product of the curve's code through pointers to the \
  operands and the result: word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh`, \
  the accumulator in registers, four words of `[b]` in registers and the others loaded), each \
  reduction step multiplying the accumulator's low word by `-m⁻¹ mod 2⁶⁴` and adding that \
  multiple of the modulus, then a final conditional subtraction selected by `csel`."]

def artifacts : List Artifact := [
  { p384p.mulApi with
    target := AArch64.target
    doc := p384p.mulApi.doc (notes := notes)
    code := mulFn p384p.k p384p.m
    contract := p384p.mulContract AArch64.abi
    verified := p384p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521p.mulApi with
    target := AArch64.target
    doc := p521p.mulApi.doc (notes := notes)
    code := mulFn p521p.k p521p.m
    contract := p521p.mulContract AArch64.abi
    verified := p521p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p384n.mulApi with
    target := AArch64.target
    doc := p384n.mulApi.doc (notes := notesG)
    code := mulFn p384n.k p384n.m
    contract := p384n.mulContract AArch64.abi
    verified := p384n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521n.mulApi with
    target := AArch64.target
    doc := p521n.mulApi.doc (notes := notesG)
    code := mulFn p521n.k p521n.m
    contract := p521n.mulContract AArch64.abi
    verified := p521n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }
]

end VG.Artifacts.WeierstrassMont.AArch64
