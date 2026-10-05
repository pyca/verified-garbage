import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM-SIV: GHASH's product with `x`

Untrusted: everything here is checked by Lean. `mulXG`, the key with which
GHASH computes POLYVAL (`Proof.GcmSiv.Polyval.polyvalFrom_eq`), in a module
of its own, so that code computing it need not import the algebra that
relates the two.
-/

namespace VG.Proof.GcmSiv.Polyval

/-- GHASH's product with `x`: a shift to the right (`Proof.Gcm.Poly.φ_shr1`). -/
def mulXG (h : Spec.Gcm.Block) : Spec.Gcm.Block :=
  if h.getLsbD 0 then (h >>> 1) ^^^ Spec.Gcm.R else h >>> 1

end VG.Proof.GcmSiv.Polyval
