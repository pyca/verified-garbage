module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
public import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP384r1
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.X25519.X86.Column

/-! # Montgomery arithmetic modulo brainpoolP384r1's `p` and `n` on x86 (32-bit)

The functions of `Artifacts/WeierstrassMont/X86.lean` for brainpoolP384r1's moduli,
in six 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontBrainpoolP384r1.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `ebp` (and the product `ebx`, `esi` and `edi`) in \
  its own working space and addresses it through `ebp`, `[a]` and `[b]` through pointers, and \
  `[o]` through `ecx`. The numbers are 32-bit words: the product is word-by-word Montgomery \
  multiplication (CIOS, unrolled, with `mul`, the modulus as immediates and the accumulator in \
  the own working space), and every result is reduced by a conditional subtraction selected by \
  a mask."]

def artifacts : List Artifact := [
  { brainpoolp384r1p.mulApi with
    target := X86.target
    doc := brainpoolp384r1p.mulApi.doc (notes := notes)
    code := mulFn brainpoolp384r1p.k brainpoolp384r1p.m
    contract := brainpoolp384r1p.mulContract X86.abi
    verified := brainpoolp384r1p_mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { brainpoolp384r1p.addApi with
    target := X86.target
    doc := brainpoolp384r1p.addApi.doc (notes := notes)
    code := addFn brainpoolp384r1p.k brainpoolp384r1p.m
    contract := brainpoolp384r1p.addContract X86.abi
    verified := brainpoolp384r1p_add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { brainpoolp384r1p.subApi with
    target := X86.target
    doc := brainpoolp384r1p.subApi.doc (notes := notes)
    code := subFn brainpoolp384r1p.k brainpoolp384r1p.m
    contract := brainpoolp384r1p.subContract X86.abi
    verified := brainpoolp384r1p_sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { brainpoolp384r1n.mulApi with
    target := X86.target
    doc := brainpoolp384r1n.mulApi.doc (notes := notes)
    code := mulFn brainpoolp384r1n.k brainpoolp384r1n.m
    contract := brainpoolp384r1n.mulContract X86.abi
    verified := brainpoolp384r1n_mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { brainpoolp384r1n.addApi with
    target := X86.target
    doc := brainpoolp384r1n.addApi.doc (notes := notes)
    code := addFn brainpoolp384r1n.k brainpoolp384r1n.m
    contract := brainpoolp384r1n.addContract X86.abi
    verified := brainpoolp384r1n_add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { brainpoolp384r1n.subApi with
    target := X86.target
    doc := brainpoolp384r1n.subApi.doc (notes := notes)
    code := subFn brainpoolp384r1n.k brainpoolp384r1n.m
    contract := brainpoolp384r1n.subContract X86.abi
    verified := brainpoolp384r1n_sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.WeierstrassMontBrainpoolP384r1.X86
