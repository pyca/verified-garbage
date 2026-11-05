module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES: the contracts of the block functions on the key schedule they are given

Not trusted: the contracts that the proofs of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are written against,
for the key schedule and the number of rounds they are given, whatever key
that schedule came from. The shared contracts in `Spec/` are stated for
every AES key whose schedule is in memory with its number of rounds
(`Spec.Aes.KeySchedule`), and follow from these (`Verified.post_mono`): with
the schedule of a key and its rounds, the cipher of the schedule is AES with
that key.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.Spec
open VG.Spec.Aes

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces each of the `n` blocks at
`data` with `CIPHER(·, rounds, w)`. The key schedule and the data are
secret. -/
def encryptBlocksRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (pre := fun _schedule rounds _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds data n _scratch m m' _ =>
      statesAt m' data n.toNat =
        (statesAt m data n.toNat).map
          (cipher rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1)))))
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces each of the `n` blocks at
`data` with `INVCIPHER(·, rounds, w)`. The key schedule and the data are
secret. -/
def decryptBlocksRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (pre := fun _schedule rounds _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds data n _scratch m m' _ =>
      statesAt m' data n.toNat =
        (statesAt m data n.toNat).map
          (invCipher rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1)))))
    (stack := stack)

/-- `Spec.Aes.encryptBlocksContract` from `encryptBlocksRoundsContract`. -/
theorem encryptBlocks_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (encryptBlocksRoundsContract A stack)) : Verified T c (Spec.Aes.encryptBlocksContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Aes.decryptBlocksContract` from `decryptBlocksRoundsContract`. -/
theorem decryptBlocks_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (decryptBlocksRoundsContract A stack)) : Verified T c (Spec.Aes.decryptBlocksContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

end VG.Proof.Aes
