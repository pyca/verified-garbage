module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1

/-! # Montgomery arithmetic modulo brainpoolP512r1's `p` and `n` on x86 (32-bit)

The functions of `Artifacts/WeierstrassMont/X86.lean` for brainpoolP512r1's moduli,
in eight 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `ebp` (and the product `ebx`, `esi` and `edi`) in \
  its own working space and addresses it through `ebp`, `[a]` and `[b]` through pointers, and \
  `[o]` through `ecx`. The numbers are 32-bit words: the product is word-by-word Montgomery \
  multiplication (CIOS, unrolled, with `mul`, the modulus as immediates and the accumulator in \
  the own working space), and every result is reduced by a conditional subtraction selected by \
  a mask."]

def artifacts : List Artifact := [
  brainpoolp512r1p.mulApi.artifact X86.target {
    notes := notes
    code := mulFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_mul_verified },
  brainpoolp512r1p.addApi.artifact X86.target {
    notes := notes
    code := addFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_add_verified },
  brainpoolp512r1p.subApi.artifact X86.target {
    notes := notes
    code := subFn brainpoolp512r1p.k brainpoolp512r1p.m
    verified := brainpoolp512r1p_sub_verified },
  brainpoolp512r1n.mulApi.artifact X86.target {
    notes := notes
    code := mulFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_mul_verified },
  brainpoolp512r1n.addApi.artifact X86.target {
    notes := notes
    code := addFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_add_verified },
  brainpoolp512r1n.subApi.artifact X86.target {
    notes := notes
    code := subFn brainpoolp512r1n.k brainpoolp512r1n.m
    verified := brainpoolp512r1n_sub_verified }]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.X86
