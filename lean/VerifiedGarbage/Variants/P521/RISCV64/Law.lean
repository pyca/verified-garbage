module

public import VerifiedGarbage.Proof.P521.Curve
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-521's group law, on RISCV64 -/

@[expose] public section

namespace VG.Variants.P521.RISCV64.Law

def variant : Proof.Weierstrass.HasLaw Spec.P521.curve := ⟨Proof.P521.law⟩

end VG.Variants.P521.RISCV64.Law
