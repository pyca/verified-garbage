module

public import VerifiedGarbage.Proof.Variants.Sha1.X86.Scalar

/-! # SHA-1 on x86: the scalar compression function -/

@[expose] public section

namespace VG.Variants.Sha1.X86.Scalar

def variant : Proof.Sha1.X86.Variants.Backend := Proof.Variants.Sha1.X86.Scalar.variant

end VG.Variants.Sha1.X86.Scalar
