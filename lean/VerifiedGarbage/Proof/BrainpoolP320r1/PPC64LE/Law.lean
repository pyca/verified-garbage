module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.BrainpoolP320r1
import VerifiedGarbage.Proof.BrainpoolP320r1.Curve
import VerifiedGarbage.Proof.BrainpoolP320r1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # brainpoolP320r1's group law, on PPC64LE -/

public section

namespace VG.Proof.BrainpoolP320r1.PPC64LE

/-- brainpoolP320r1's group law, on PPC64LE, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.BrainpoolP320r1.curve := ⟨Proof.BrainpoolP320r1.law⟩

end VG.Proof.BrainpoolP320r1.PPC64LE
