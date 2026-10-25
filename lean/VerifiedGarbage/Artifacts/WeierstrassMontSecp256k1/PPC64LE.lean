module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontSecp256k1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo secp256k1's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for secp256k1's moduli, in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontSecp256k1.PPC64LE

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
  secp256k1p.mulApi.artifact PPC64LE.target {
    notes := notes
    code := mulFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_mul_verified },
  secp256k1p.addApi.artifact PPC64LE.target {
    notes := notes
    code := addFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_add_verified },
  secp256k1p.subApi.artifact PPC64LE.target {
    notes := notes
    code := subFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_sub_verified },
  secp256k1n.mulApi.artifact PPC64LE.target {
    notes := notes
    code := mulFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_mul_verified },
  secp256k1n.addApi.artifact PPC64LE.target {
    notes := notes
    code := addFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_add_verified },
  secp256k1n.subApi.artifact PPC64LE.target {
    notes := notes
    code := subFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_sub_verified }]

end VG.Artifacts.WeierstrassMontSecp256k1.PPC64LE
