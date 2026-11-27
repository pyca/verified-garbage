module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.BrainpoolP256r1
import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # brainpoolP256r1's group law, on RISCV64 -/

public section

namespace VG.Proof.BrainpoolP256r1.RISCV64

/-- brainpoolP256r1's group law, on RISCV64, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve := ⟨Proof.BrainpoolP256r1.law⟩

end VG.Proof.BrainpoolP256r1.RISCV64
