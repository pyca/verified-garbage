module

public import VerifiedGarbage.Proof.Blake2.X86_64.Variants.Blake2bScalar

/-! # BLAKE2b on baseline x86-64 -/

@[expose] public section

namespace VG.Variants.Blake2b.X86_64.Scalar

def variant : Proof.Blake2.X86_64.Backend := Proof.Blake2.X86_64.Variants.Blake2bScalar.variant

end VG.Variants.Blake2b.X86_64.Scalar
