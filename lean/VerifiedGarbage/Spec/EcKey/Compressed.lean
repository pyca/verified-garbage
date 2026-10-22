module

public import VerifiedGarbage.Spec.EcKey

/-!
# Compressed SEC 1 public points

**Trusted** (as every file in `Spec/`). SEC 1 v2.0 §2.3.3 encodes a finite
point as `02 ‖ x` for even `y`, and `03 ‖ x` for odd `y`, with `x` in
exactly `len` octets, most significant first. Section 2.3.4 recovers `y`
from `y² = x³ + a x + b` and the tag's parity bit.

`matchesCompressedPublicKey` states that relation directly, without choosing
a square-root algorithm. In particular, a decoder must reject a nonsquare
right-hand side, and cannot accept odd parity when the only root is zero.
The relation checks the exact length, tag, canonical field coordinate and
curve equation, and rejects infinity. As in `EcKey.decodePublicKey`, the
supported curves have cofactor one, so no subgroup multiplication is needed.

This is additive: the existing uncompressed encoder, decoder, ECDH and
ECDSA contracts keep their meanings.
-/

@[expose] public section

namespace VG.Spec.EcKey

open Weierstrass

/-- SEC 1 §2.3.3 with point compression: `00` for infinity, otherwise
`(02 + (y mod 2)) ‖ x`. Public-key conversion rejects infinity. -/
def encodeCompressedPoint {C : Curve} : Point C → List Byte
  | .infinity => [0]
  | .affine x y => BitVec.ofNat 8 (2 + y.val % 2) :: toBytes C.len x.val

/-- SEC 1 §2.3.4 for a compressed, validated public key. Expressing the
recovered point as a relation leaves the square-root method to the
implementation. Field elements are `Fin p`, so the decoded `x` must be
strictly below `p`; reduction of a noncanonical encoding is not allowed. -/
def matchesCompressedPublicKey (C : Curve) (bs : List Byte) : Point C → Prop
  | .infinity => False
  | .affine x y =>
    bs.length = C.len + 1 ∧
    bs.head? = some (BitVec.ofNat 8 (2 + y.val % 2)) ∧
    ofBytes (bs.drop 1) = x.val ∧
    onCurve C (.affine x y) = true

instance (C : Curve) (bs : List Byte) (Q : Point C) :
    Decidable (matchesCompressedPublicKey C bs Q) := by
  cases Q <;> unfold matchesCompressedPublicKey <;> infer_instance

/-- Validate an uncompressed public key, then compress it (SEC 1 §2.3.3).
Malformed encodings, infinity and off-curve points are rejected by the
existing uncompressed decoder. -/
def compressPublicKey (C : Curve) (bs : List Byte) : Option (List Byte) :=
  (decodePublicKey C bs).map encodeCompressedPoint

end VG.Spec.EcKey
