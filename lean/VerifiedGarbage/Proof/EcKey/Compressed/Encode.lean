module

public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Proof.Ecdh.Exchange

/-! # Compression of a checked pair of canonical coordinates -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed

open Spec.Weierstrass Spec.EcKey

theorem compress_eq {C : Curve} {bs : List Byte} (hlen : bs.length = 2 * C.len + 1)
    {b0 : Byte} (hb0 : bs.head? = some b0) {x y : Nat}
    (hx : ofBytes ((bs.drop 1).take C.len) = x) (hy : ofBytes (bs.drop (C.len + 1)) = y) :
    compressPublicKey C bs = if Proof.Ecdh.Valid C b0 x y then
      some (BitVec.ofNat 8 (2 + y % 2) :: toBytes C.len x) else none := by
  rw [compressPublicKey, Proof.Ecdh.decode_eq hlen hb0 hx hy]
  split <;> rfl

end VG.Proof.EcKey.Compressed
