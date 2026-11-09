module

public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-CFB8: the contracts on the key schedule they are given

Not trusted: the contracts that the proofs of `vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt` are written against,
for the key schedule and the number of rounds they are given, whatever key
that schedule came from. The shared contracts in `Spec/` are stated for
every AES key whose schedule is in memory with its number of rounds
(`Spec.Aes.KeySchedule`), and follow from these (`Verified.post_mono`): with
the schedule of a key and its rounds, the cipher of the schedule is AES with
that key.
-/

@[expose] public section

namespace VG.Proof.AesCfb8

open VG.Spec
open VG.Spec.Cfb8

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their CFB8 encryption (§6.3) by AES with `w`, from the input block at
`iv`, and that block with the input block of the next byte, its last
`16 - len` bytes followed by the last `len` (up to 16) ciphertext bytes
(unchanged if `len = 0`). -/
def encryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := encrypt ciph (Aes.bytesAt m iv 16) (Aes.bytesAt m data len.toNat)
      Aes.bytesAt m' data len.toNat = cs ∧ Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their CFB8 decryption (§6.3) by AES with `w`, from the input block at
`iv`, and that block with the input block of the next byte, its last
`16 - len` bytes followed by the last `len` (up to 16) bytes at `data` on
entry (unchanged if `len = 0`). -/
def decryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := Aes.bytesAt m data len.toNat
      Aes.bytesAt m' data len.toNat = decrypt ciph (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- `Spec.Cfb8.aesEncryptContract` from `encryptRoundsContract`. -/
theorem encrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (encryptRoundsContract A stack)) : Verified T c (Spec.Cfb8.aesEncryptContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cfb8.aesDecryptContract` from `decryptRoundsContract`. -/
theorem decrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (decryptRoundsContract A stack)) : Verified T c (Spec.Cfb8.aesDecryptContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

end VG.Proof.AesCfb8
