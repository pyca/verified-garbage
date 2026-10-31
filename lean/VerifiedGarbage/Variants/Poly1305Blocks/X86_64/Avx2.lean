module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Variant
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # `vg_poly1305_blocks` on x86-64: with AVX2 -/

@[expose] public section

namespace VG.Variants.Poly1305Blocks.X86_64.Avx2

def variant : Proof.Poly1305.X86_64.BlocksImpl := .avx2

end VG.Variants.Poly1305Blocks.X86_64.Avx2
