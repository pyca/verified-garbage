module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1

/-! # Montgomery arithmetic modulo secp256k1's `p` and `n` on x86 (32-bit)

The functions of `Artifacts/WeierstrassMont/X86.lean` for secp256k1's moduli,
in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontSecp256k1.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `ebp` (and the product `ebx`, `esi` and `edi`) in \
  its own working space and addresses it through `ebp`, `[a]` and `[b]` through pointers, and \
  `[o]` through `ecx`. The numbers are 32-bit words: the product is word-by-word Montgomery \
  multiplication (CIOS, unrolled, with `mul`, the modulus as immediates and the accumulator in \
  the own working space), and every result is reduced by a conditional subtraction selected by \
  a mask."]

def artifacts : List Artifact := [
  secp256k1p.mulApi.artifact X86.target {
    notes := notes
    code := mulFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_mul_verified },
  secp256k1p.addApi.artifact X86.target {
    notes := notes
    code := addFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_add_verified },
  secp256k1p.subApi.artifact X86.target {
    notes := notes
    code := subFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_sub_verified },
  secp256k1n.mulApi.artifact X86.target {
    notes := notes
    code := mulFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_mul_verified },
  secp256k1n.addApi.artifact X86.target {
    notes := notes
    code := addFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_add_verified },
  secp256k1n.subApi.artifact X86.target {
    notes := notes
    code := subFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_sub_verified }]

end VG.Artifacts.WeierstrassMontSecp256k1.X86
