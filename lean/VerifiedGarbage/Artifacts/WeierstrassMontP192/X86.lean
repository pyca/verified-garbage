module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontP192
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on x86 (32-bit)

The functions of `Artifacts/WeierstrassMont/X86.lean` for P-192's moduli,
in three 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontP192.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `ebp` (and the product `ebx`, `esi` and `edi`) in \
  its own working space and addresses it through `ebp`, `[a]` and `[b]` through pointers, and \
  `[o]` through `ecx`. The numbers are 32-bit words: the product is word-by-word Montgomery \
  multiplication (CIOS, unrolled, with `mul`, the modulus as immediates and the accumulator in \
  the own working space), and every result is reduced by a conditional subtraction selected by \
  a mask."]

def artifacts : List Artifact := [
  p192p.mulApi.artifact X86.target {
    notes := notes
    code := mulFn p192p.k p192p.m
    verified := p192p_mul_verified },
  p192p.addApi.artifact X86.target {
    notes := notes
    code := addFn p192p.k p192p.m
    verified := p192p_add_verified },
  p192p.subApi.artifact X86.target {
    notes := notes
    code := subFn p192p.k p192p.m
    verified := p192p_sub_verified },
  p192n.mulApi.artifact X86.target {
    notes := notes
    code := mulFn p192n.k p192n.m
    verified := p192n_mul_verified },
  p192n.addApi.artifact X86.target {
    notes := notes
    code := addFn p192n.k p192n.m
    verified := p192n_add_verified },
  p192n.subApi.artifact X86.target {
    notes := notes
    code := subFn p192n.k p192n.m
    verified := p192n_sub_verified }]

end VG.Artifacts.WeierstrassMontP192.X86
