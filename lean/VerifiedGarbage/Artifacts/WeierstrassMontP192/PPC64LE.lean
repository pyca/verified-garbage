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
  registers `r0` and `r4`–`r12` (no frame, nothing saved). The model has no carry, so the numbers are \
  32-bit digits (the 32-bit words of the numbers, `lwz` and `stw`) in 64-bit registers: a digit times a \
  digit plus a digit and a carry fits in 64 bits. The product is digit-by-digit Montgomery \
  multiplication (CIOS, with `mulld` and the accumulator in the own working space, one row of `[b]` and \
  one of the modulus for each digit of `[a]`, counted down in a loop), and every result is reduced by a \
  conditional subtraction selected by a mask, a 64-bit word at a time."]

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
