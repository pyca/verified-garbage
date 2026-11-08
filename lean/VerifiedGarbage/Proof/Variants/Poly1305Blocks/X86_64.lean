module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Variant
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Variant
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Variant
public import VerifiedGarbage.Proof.Poly1305.X86_64.Variant

/-! # The implementations of `Poly1305Blocks` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Poly1305Blocks.X86_64

def avx2 : Proof.Poly1305.X86_64.BlocksImpl := .avx2

def avx512 : Proof.Poly1305.X86_64.BlocksImpl := .avx512

def ifma : Proof.Poly1305.X86_64.BlocksImpl := .ifma

def scalar : Proof.Poly1305.X86_64.BlocksImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [ifma, avx512, avx2, scalar]

end VG.Proof.Variants.Poly1305Blocks.X86_64
