module

public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent, for every target's `thash4`, which a module of one target may not import from another's.

/-!
# SLH-DSA: SHAKE256 with one block of output

An output of at most one block (136 bytes) of `SHAKE256(M)` is the first
bytes of the state after absorbing the padded message: the streaming state
of `M` (`Rep`), SHAKE's suffix `0x1f` XORed into the byte at `M`'s position
in its last block and `0x80` into the block's last byte, permuted
(`absorb_pad`). That is what an implementation of `thash4` computes.
-/

@[expose] public section

namespace VG.Proof.SlhDsa

open VG.Spec.Sha3
open VG.Proof.Sha3 (Rep xorByte byteOf absorb_pad length_squeeze squeeze_getElem iterF)

/-- The state whose first bytes are `SHAKE256(M)`. -/
def finalState (M : List Byte) : State :=
  keccakF (xorByte (xorByte (Rep 136 M) (M.length % 136) 0x1f) 135 0x80)

theorem shake256_eq (M : List Byte) (d : Nat) :
    shake256 M d = squeeze 136 (absorb 136 (pad 136 0x1f M)) d := rfl

theorem length_shake256 (M : List Byte) (d : Nat) : (shake256 M d).length = d := by
  rw [shake256_eq, length_squeeze (by decide) (by decide)]

/-- Byte `i < 136` of `SHAKE256(M)` is byte `i` of `finalState M`. -/
theorem shake256_getElem (M : List Byte) {d i : Nat} (hi : i < d) (h136 : i < 136) :
    (shake256 M d)[i]'(by rw [length_shake256]; exact hi) = byteOf (finalState M) i := by
  simp only [shake256_eq]
  rw [squeeze_getElem (by decide) (by decide) _ hi, Nat.div_eq_of_lt h136, Nat.mod_eq_of_lt h136,
    absorb_pad (by decide) (by decide)]
  rfl

/-- `SHAKE256(M)` of at most 136 bytes, as a list: its bytes are those of
`finalState M`. -/
theorem shake256_ext {M : List Byte} {d : Nat} (hd : d ≤ 136) {L : List Byte} (hl : L.length = d)
    (h : ∀ i (hi : i < d), L[i]'(by rw [hl]; exact hi) = byteOf (finalState M) i) : L = shake256 M d := by
  apply List.ext_getElem (by rw [hl, length_shake256])
  intro i h₁ _
  rw [h i (by omega_using [h₁, hl]), shake256_getElem M (by omega_using [h₁, hl]) (by omega_using [h₁, hl, hd])]

end VG.Proof.SlhDsa
