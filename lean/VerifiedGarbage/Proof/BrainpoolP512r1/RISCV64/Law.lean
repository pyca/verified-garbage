module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.BrainpoolP512r1
import VerifiedGarbage.Proof.BrainpoolP512r1.Curve
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # brainpoolP512r1's group law, on RISCV64 -/

public section

namespace VG.Proof.BrainpoolP512r1.RISCV64

/-- brainpoolP512r1's group law, on RISCV64, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve := ⟨Proof.BrainpoolP512r1.law⟩

end VG.Proof.BrainpoolP512r1.RISCV64
