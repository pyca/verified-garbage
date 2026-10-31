module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Variant

/-! # `vg_poly1305_blocks` on x86-64: the scalar implementation -/

@[expose] public section

namespace VG.Variants.Poly1305Blocks.X86_64.Scalar

def variant : Proof.Poly1305.X86_64.BlocksImpl := .scalar

end VG.Variants.Poly1305Blocks.X86_64.Scalar
