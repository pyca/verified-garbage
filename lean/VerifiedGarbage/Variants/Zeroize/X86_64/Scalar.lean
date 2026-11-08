module

public import VerifiedGarbage.Proof.Zeroize.X86_64Impl

/-! # `vg_zeroize` on x86-64: the baseline -/

@[expose] public section

namespace VG.Variants.Zeroize.X86_64.Scalar

def variant : Proof.Zeroize.X86_64.ZeroizeImpl := .scalar

end VG.Variants.Zeroize.X86_64.Scalar
