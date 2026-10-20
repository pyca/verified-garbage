module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSqr521Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery products modulo the curves' `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.AArch64

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

/-- How the function for P-384's `p` works. -/
def notes384 : List String := ["The function zero-extends the offsets, saves the callee-saved \
  registers it writes in lanes of `v16`–`v20`, and keeps all of `[b]` in registers. Its schedule \
  is adapted from s2n-bignum's `bignum_montmul_p384_alt` (Apache-2.0 OR ISC OR MIT-0): the full \
  twelve-word product in registers (`mul` and `umulh`, one word of `[a]` loaded per row), then six \
  short Montgomery reductions of its low half, each multiplying by the three nonzero words of \
  `2^384 - p` rather than by `p`, then the high half added and a final conditional subtraction \
  against `p`, built in registers, selected by `csel`."]

/-- How the square modulo P-384's `p` works. -/
def notesSqr384 : List String := ["The function is the product modulo P-384's `p` (its saves, \
  reductions and final subtraction) with `[a]` loaded in place of `[b]` and a square in place of \
  the product, its schedule adapted from s2n-bignum's `bignum_montsqr_p384_alt` (Apache-2.0 OR ISC \
  OR MIT-0): the fifteen products of distinct words once (a `mul` and `umulh` row for each word), the \
  sum doubled, then the six squares of the words added."]

/-- The dedicated Mersenne-prime square uses every off-diagonal product once. -/
def notesSqr521 : List String := ["The function loads all nine input words before writing the output, \
  computes the symmetric square in registers, folds at bit 521, and conditionally corrects to \
  the canonical field residue. A cyclic 55-bit rotation supplies the Montgomery factor. \
  Callee-saved registers are kept in vector lanes; the output pointer is duplicated in v22. \
  The function has no stack frame and permits the output to alias the input."]

/-- How the functions work. -/
def notes : List String := ["The function zero-extends the offsets, saves the callee-saved \
  registers it writes in lanes of `v16`–`v20`, and keeps every word it multiplies by in a register: \
  all of `[b]`. The product is word-by-word Montgomery multiplication (CIOS, with `mul` and \
  `umulh`, the accumulator in registers, one word of `[a]` loaded per round), whose reductions \
  multiply by no word of the modulus: P-521's `p` reduces by shifts. A final conditional \
  subtraction against the modulus, built in registers (`movz`/`movk`), is selected by `csel`."]

/-- How the functions for a general modulus work. -/
def notesG : List String := ["The function zero-extends the offsets, saves the callee-saved \
  registers it writes in lanes of `v16`–`v19`, writes the modulus's words (`movz`/`movk`) into its \
  own working space, and runs the inline product of the curve's code through pointers to the \
  operands and the result: word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh`, \
  the accumulator in registers, four words of `[b]` in registers and the others loaded), each \
  reduction step multiplying the accumulator's low word by `-m⁻¹ mod 2⁶⁴` and adding that \
  multiple of the modulus, then a final conditional subtraction selected by `csel`."]

def artifacts : List Artifact := [
  p384p.mulApi.artifact AArch64.target {
    notes := notes384
    code := mulFn p384p.k p384p.m
    verified := p384p_mul_verified },
  p384p.sqrApi.artifact AArch64.target {
    notes := notesSqr384
    code := sqrFn384
    verified := p384p_sqr_verified },
  p521p.sqrApi.artifact AArch64.target {
    notes := notesSqr521
    code := sqrFn521
    verified := p521p_sqr_verified },
  p521p.mulApi.artifact AArch64.target {
    notes := notes
    code := mulFn p521p.k p521p.m
    verified := p521p_mul_verified },
  p384n.mulApi.artifact AArch64.target {
    notes := notesG
    code := mulFn p384n.k p384n.m
    verified := p384n_mul_verified },
  p521n.mulApi.artifact AArch64.target {
    notes := notesG
    code := mulFn p521n.k p521n.m
    verified := p521n_mul_verified }
]

end VG.Artifacts.WeierstrassMont.AArch64
