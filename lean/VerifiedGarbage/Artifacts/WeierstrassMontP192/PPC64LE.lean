module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontP192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for P-192's moduli, in three 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontP192.PPC64LE

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Mont

/-- How the functions work. -/
def notes : List String := ["The function zero-extends the offsets, stores the modulus in its own \
  working space, and reads `[a]` and `[b]` and writes `[o]` through pointers, using only the volatile \
  registers `r0` and `r4`–`r12` (no frame, nothing saved). The numbers are 64-bit words: `mulld` and \
  `mulhdu` give the low and high words of a product, and `addc`, `adde`, `addze`, `subfc` and `subfe` \
  add and subtract with XER's carry. The product is word-by-word Montgomery multiplication (CIOS, with \
  the accumulator in the own working space, one row of `[b]` and one of the modulus for each word of \
  `[a]`, counted down in a loop), and every result is reduced by a conditional subtraction selected by \
  a mask, a word at a time."]

def artifacts : List Artifact := [
  p192p.mulApi.artifact PPC64LE.target {
    notes := notes
    code := mulFn p192p.k p192p.m
    verified := p192p_mul_verified },
  p192p.addApi.artifact PPC64LE.target {
    notes := notes
    code := addFn p192p.k p192p.m
    verified := p192p_add_verified },
  p192p.subApi.artifact PPC64LE.target {
    notes := notes
    code := subFn p192p.k p192p.m
    verified := p192p_sub_verified },
  p192n.mulApi.artifact PPC64LE.target {
    notes := notes
    code := mulFn p192n.k p192n.m
    verified := p192n_mul_verified },
  p192n.addApi.artifact PPC64LE.target {
    notes := notes
    code := addFn p192n.k p192n.m
    verified := p192n_add_verified },
  p192n.subApi.artifact PPC64LE.target {
    notes := notes
    code := subFn p192n.k p192n.m
    verified := p192n_sub_verified }]

end VG.Artifacts.WeierstrassMontP192.PPC64LE
