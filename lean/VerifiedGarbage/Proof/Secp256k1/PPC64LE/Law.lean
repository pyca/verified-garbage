module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Secp256k1
import VerifiedGarbage.Proof.Secp256k1.Curve
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # secp256k1's group law, on PPC64LE -/

public section

namespace VG.Proof.Secp256k1.PPC64LE

/-- secp256k1's group law, on PPC64LE, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve := ⟨Proof.Secp256k1.law⟩

end VG.Proof.Secp256k1.PPC64LE
