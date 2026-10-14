module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Spec.Rc2

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
  { secp256k1p.mulApi with
    target := X86.target
    doc := secp256k1p.mulApi.doc (notes := notes)
    code := mulFn secp256k1p.k secp256k1p.m
    contract := secp256k1p.mulContract X86.abi
    verified := secp256k1p_mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { secp256k1p.addApi with
    target := X86.target
    doc := secp256k1p.addApi.doc (notes := notes)
    code := addFn secp256k1p.k secp256k1p.m
    contract := secp256k1p.addContract X86.abi
    verified := secp256k1p_add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { secp256k1p.subApi with
    target := X86.target
    doc := secp256k1p.subApi.doc (notes := notes)
    code := subFn secp256k1p.k secp256k1p.m
    contract := secp256k1p.subContract X86.abi
    verified := secp256k1p_sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { secp256k1n.mulApi with
    target := X86.target
    doc := secp256k1n.mulApi.doc (notes := notes)
    code := mulFn secp256k1n.k secp256k1n.m
    contract := secp256k1n.mulContract X86.abi
    verified := secp256k1n_mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { secp256k1n.addApi with
    target := X86.target
    doc := secp256k1n.addApi.doc (notes := notes)
    code := addFn secp256k1n.k secp256k1n.m
    contract := secp256k1n.addContract X86.abi
    verified := secp256k1n_add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { secp256k1n.subApi with
    target := X86.target
    doc := secp256k1n.subApi.doc (notes := notes)
    code := subFn secp256k1n.k secp256k1n.m
    contract := secp256k1n.subContract X86.abi
    verified := secp256k1n_sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.WeierstrassMontSecp256k1.X86
