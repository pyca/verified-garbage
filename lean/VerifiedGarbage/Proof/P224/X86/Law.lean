module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Proof.P224.Curve
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-224's group law, on x86 (32-bit) -/

public section

namespace VG.Proof.P224.X86

/-- P-224's group law, on x86 (32-bit), which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.P224.curve := ⟨Proof.P224.law⟩

end VG.Proof.P224.X86
