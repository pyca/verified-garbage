module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo brainpoolP256r1's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for brainpoolP256r1's moduli, in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP256r1.PPC64LE

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
  brainpoolp256r1p.mulApi.artifact PPC64LE.target {
    notes := notes
    code := mulFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_mul_verified },
  brainpoolp256r1p.addApi.artifact PPC64LE.target {
    notes := notes
    code := addFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_add_verified },
  brainpoolp256r1p.subApi.artifact PPC64LE.target {
    notes := notes
    code := subFn brainpoolp256r1p.k brainpoolp256r1p.m
    verified := brainpoolp256r1p_sub_verified },
  brainpoolp256r1n.mulApi.artifact PPC64LE.target {
    notes := notes
    code := mulFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_mul_verified },
  brainpoolp256r1n.addApi.artifact PPC64LE.target {
    notes := notes
    code := addFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_add_verified },
  brainpoolp256r1n.subApi.artifact PPC64LE.target {
    notes := notes
    code := subFn brainpoolp256r1n.k brainpoolp256r1n.m
    verified := brainpoolp256r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP256r1.PPC64LE
