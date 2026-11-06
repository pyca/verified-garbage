module

public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Spec.Ed25519

/-!
# Cached points

The form `[Y - X, Y + X, 2dT, 2Z]` in which the tables of points to add keep
them (`cache`).
-/

@[expose] public section

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519

/-- `[Y - X, Y + X, 2dT, 2Z]`: a point cached for addition. -/
def cache (q : Point) : Point := ⟨q.Y - q.X, q.Y + q.X, q.T * 2 * d, q.Z * 2⟩

end VG.Proof.Ed25519
