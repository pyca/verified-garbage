module

public import VerifiedGarbage.Proof.Variants.Sha256.X86.Scalar

/-! # SHA-256 on x86: the scalar compression function -/

@[expose] public section

namespace VG.Variants.Sha256.X86.Scalar

def variant : Proof.Sha256.X86.Variants.Backend := Proof.Variants.Sha256.X86.Scalar.variant

end VG.Variants.Sha256.X86.Scalar
