import VerifiedGarbage.Proof.Ed448.Prune

/-!
# Ed448: pruning a scalar, on bytes

`Spec.Ed448.prune` (clear bits 0–1 and 448–455, set bit 447) on a number
given as its first byte, the 54 bytes after it (`M`), and its bytes 55 and
56: byte 0 with bits 0–1 cleared, byte 55 with bit 7 set, and byte 56 zero
(`prune_bytes`). Like `Prune.lean`, this module imports only Lean core.
-/

namespace VG.Proof.Ed448

theorem prune_bytes {b0 M b55 b56 : Nat} (h0 : b0 < 256) (hM : M < 2 ^ 432) (h55 : b55 < 256) :
    ((b0 + 256 * (M + 2 ^ 432 * (b55 + 256 * b56))) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 =
      (b0 &&& 252) + 256 * (M + 2 ^ 432 * ((b55 ||| 128) + 256 * 0)) := by
  rw [and_sub4 _ 448 (by omega), show (252 : Nat) = 2 ^ 8 - 4 from rfl, and_sub4 b0 8 (by omega),
    or_pow_eq (k := 447) (by omega), show (128 : Nat) = 2 ^ 7 from rfl, or_pow_eq (k := 7) (by omega)]
  simp only [show 448 - 2 = 446 from rfl, show 8 - 2 = 6 from rfl]
  omega

end VG.Proof.Ed448
