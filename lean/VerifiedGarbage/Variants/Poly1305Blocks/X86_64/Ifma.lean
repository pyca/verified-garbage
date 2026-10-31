module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Variant
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # `vg_poly1305_blocks` on x86-64: with AVX-512 IFMA -/

@[expose] public section

namespace VG.Variants.Poly1305Blocks.X86_64.Ifma

def variant : Proof.Poly1305.X86_64.BlocksImpl := .ifma

end VG.Variants.Poly1305Blocks.X86_64.Ifma
