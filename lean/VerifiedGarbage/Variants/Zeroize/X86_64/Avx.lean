module

public import VerifiedGarbage.Proof.Zeroize.X86_64Impl

/-! # `vg_zeroize` on x86-64: with AVX -/

@[expose] public section

namespace VG.Variants.Zeroize.X86_64.Avx

def variant : Proof.Zeroize.X86_64.ZeroizeImpl := .avx

end VG.Variants.Zeroize.X86_64.Avx
