module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Proof.P521.Curve

/-! # P-521's group law, on RISCV64 -/

public section

namespace VG.Proof.P521.RISCV64

/-- P-521's group law, on RISCV64, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.P521.curve := ⟨Proof.P521.law⟩

end VG.Proof.P521.RISCV64
