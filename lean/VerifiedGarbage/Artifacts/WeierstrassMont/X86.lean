import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified

/-! # Montgomery arithmetic modulo the curves' `p` and `n` on x86 (32-bit) -/

namespace VG.Artifacts.WeierstrassMont.X86

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86.Mont VG.Proof.Weierstrass.X86.Mont

/-- How the functions work. -/
def notes : List String := ["The function saves `ebp` (and the product `ebx`, `esi` and `edi`) in \
  its own working space and addresses it through `ebp`, `[a]` and `[b]` through pointers, and \
  `[o]` through `ecx`. The numbers are 32-bit words: the product is word-by-word Montgomery \
  multiplication (CIOS, unrolled, with `mul`, the modulus as immediates and the accumulator in \
  the own working space; P-256's `p` reduces by its sparse form), and every result is reduced by \
  a conditional subtraction selected by a mask."]

def artifacts : List Artifact := [
  { p224p.mulApi with
    target := X86.target
    doc := p224p.mulApi.doc (notes := notes)
    code := mulFn p224p.k p224p.m
    contract := p224p.mulContract X86.abi
    verified := p224p_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p224p.addApi with
    target := X86.target
    doc := p224p.addApi.doc (notes := notes)
    code := addFn p224p.k p224p.m
    contract := p224p.addContract X86.abi
    verified := p224p_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p224p.subApi with
    target := X86.target
    doc := p224p.subApi.doc (notes := notes)
    code := subFn p224p.k p224p.m
    contract := p224p.subContract X86.abi
    verified := p224p_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p224n.mulApi with
    target := X86.target
    doc := p224n.mulApi.doc (notes := notes)
    code := mulFn p224n.k p224n.m
    contract := p224n.mulContract X86.abi
    verified := p224n_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p224n.addApi with
    target := X86.target
    doc := p224n.addApi.doc (notes := notes)
    code := addFn p224n.k p224n.m
    contract := p224n.addContract X86.abi
    verified := p224n_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p224n.subApi with
    target := X86.target
    doc := p224n.subApi.doc (notes := notes)
    code := subFn p224n.k p224n.m
    contract := p224n.subContract X86.abi
    verified := p224n_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p256p.mulApi with
    target := X86.target
    doc := p256p.mulApi.doc (notes := notes)
    code := mulFn p256p.k p256p.m
    contract := p256p.mulContract X86.abi
    verified := p256p_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p256p.addApi with
    target := X86.target
    doc := p256p.addApi.doc (notes := notes)
    code := addFn p256p.k p256p.m
    contract := p256p.addContract X86.abi
    verified := p256p_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p256p.subApi with
    target := X86.target
    doc := p256p.subApi.doc (notes := notes)
    code := subFn p256p.k p256p.m
    contract := p256p.subContract X86.abi
    verified := p256p_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p256n.mulApi with
    target := X86.target
    doc := p256n.mulApi.doc (notes := notes)
    code := mulFn p256n.k p256n.m
    contract := p256n.mulContract X86.abi
    verified := p256n_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p256n.addApi with
    target := X86.target
    doc := p256n.addApi.doc (notes := notes)
    code := addFn p256n.k p256n.m
    contract := p256n.addContract X86.abi
    verified := p256n_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p256n.subApi with
    target := X86.target
    doc := p256n.subApi.doc (notes := notes)
    code := subFn p256n.k p256n.m
    contract := p256n.subContract X86.abi
    verified := p256n_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384p.mulApi with
    target := X86.target
    doc := p384p.mulApi.doc (notes := notes)
    code := mulFn p384p.k p384p.m
    contract := p384p.mulContract X86.abi
    verified := p384p_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384p.addApi with
    target := X86.target
    doc := p384p.addApi.doc (notes := notes)
    code := addFn p384p.k p384p.m
    contract := p384p.addContract X86.abi
    verified := p384p_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384p.subApi with
    target := X86.target
    doc := p384p.subApi.doc (notes := notes)
    code := subFn p384p.k p384p.m
    contract := p384p.subContract X86.abi
    verified := p384p_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384n.mulApi with
    target := X86.target
    doc := p384n.mulApi.doc (notes := notes)
    code := mulFn p384n.k p384n.m
    contract := p384n.mulContract X86.abi
    verified := p384n_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384n.addApi with
    target := X86.target
    doc := p384n.addApi.doc (notes := notes)
    code := addFn p384n.k p384n.m
    contract := p384n.addContract X86.abi
    verified := p384n_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384n.subApi with
    target := X86.target
    doc := p384n.subApi.doc (notes := notes)
    code := subFn p384n.k p384n.m
    contract := p384n.subContract X86.abi
    verified := p384n_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521p.mulApi with
    target := X86.target
    doc := p521p.mulApi.doc (notes := notes)
    code := mulFn p521p.k p521p.m
    contract := p521p.mulContract X86.abi
    verified := p521p_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521p.addApi with
    target := X86.target
    doc := p521p.addApi.doc (notes := notes)
    code := addFn p521p.k p521p.m
    contract := p521p.addContract X86.abi
    verified := p521p_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521p.subApi with
    target := X86.target
    doc := p521p.subApi.doc (notes := notes)
    code := subFn p521p.k p521p.m
    contract := p521p.subContract X86.abi
    verified := p521p_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521n.mulApi with
    target := X86.target
    doc := p521n.mulApi.doc (notes := notes)
    code := mulFn p521n.k p521n.m
    contract := p521n.mulContract X86.abi
    verified := p521n_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521n.addApi with
    target := X86.target
    doc := p521n.addApi.doc (notes := notes)
    code := addFn p521n.k p521n.m
    contract := p521n.addContract X86.abi
    verified := p521n_add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521n.subApi with
    target := X86.target
    doc := p521n.subApi.doc (notes := notes)
    code := subFn p521n.k p521n.m
    contract := p521n.subContract X86.abi
    verified := p521n_sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.WeierstrassMont.X86
