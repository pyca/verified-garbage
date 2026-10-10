import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Weierstrass.X86.MontP192

/-! # Montgomery arithmetic modulo P-192's `p` and `n` on x86 (32-bit)

The functions of `Artifacts/WeierstrassMont/X86.lean` for P-192's moduli,
in three 64-bit words. -/

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
  { p192p.mulApi with
    target := X86.target
    doc := p192p.mulApi.doc (notes := notes)
    code := mulFn p192p.k p192p.m
    contract := p192p.mulContract X86.abi
    verified := p192p_mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { p192p.addApi with
    target := X86.target
    doc := p192p.addApi.doc (notes := notes)
    code := addFn p192p.k p192p.m
    contract := p192p.addContract X86.abi
    verified := p192p_add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { p192p.subApi with
    target := X86.target
    doc := p192p.subApi.doc (notes := notes)
    code := subFn p192p.k p192p.m
    contract := p192p.subContract X86.abi
    verified := p192p_sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { p192n.mulApi with
    target := X86.target
    doc := p192n.mulApi.doc (notes := notes)
    code := mulFn p192n.k p192n.m
    contract := p192n.mulContract X86.abi
    verified := p192n_mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { p192n.addApi with
    target := X86.target
    doc := p192n.addApi.doc (notes := notes)
    code := addFn p192n.k p192n.m
    contract := p192n.addContract X86.abi
    verified := p192n_add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { p192n.subApi with
    target := X86.target
    doc := p192n.subApi.doc (notes := notes)
    code := subFn p192n.k p192n.m
    contract := p192n.subContract X86.abi
    verified := p192n_sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.WeierstrassMontP192.X86
