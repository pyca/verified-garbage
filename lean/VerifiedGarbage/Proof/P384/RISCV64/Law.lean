module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.P384
import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-384's group law, on RISCV64 -/

public section

namespace VG.Proof.P384.RISCV64

/-- P-384's group law, on RISCV64, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.P384.curve := ⟨Proof.P384.law⟩

end VG.Proof.P384.RISCV64
