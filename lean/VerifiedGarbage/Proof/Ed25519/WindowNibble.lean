module
public import VerifiedGarbage.Proof.Ed25519.Group.Extended

public import VerifiedGarbage.Proof.Ed25519.ScalarBytes

/-!
# Verification with windows, nibble by nibble

Target-independent facts for windows taken one nibble at a time: a window
takes the sum of the nibbles from `i + 1` up to that from `i`
(`nibble_step`). That nibble `i` of a little-endian scalar is its base-16
digit `i`, read from byte `i / 2` (`decodeLE_nibble`), is in
`ScalarBytes.lean`, apart from the group's algebra.
-/

@[expose] public section

namespace VG.Proof.Ed25519

open Edwards

/-- The windows' sum, one nibble on: `16` times the sum so far plus the digits. -/
theorem nibble_step (A N : EPoint dZ) (K S i : Nat) :
    (16 : Nat) • ((K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • N) + (K / 16 ^ i % 16) • A +
      (S / 16 ^ i % 16) • N = (K / 16 ^ i) • A + (S / 16 ^ i) • N := by
  have hK := nibble_split K i
  have hS := nibble_split S i
  generalize K / 16 ^ i % 16 = kr at hK ⊢
  generalize S / 16 ^ i % 16 = sr at hS ⊢
  rw [hK, hS, smul_add, ← mul_nsmul', ← mul_nsmul', add_nsmul, add_nsmul, add_assoc, add_add_add_comm]

end VG.Proof.Ed25519
