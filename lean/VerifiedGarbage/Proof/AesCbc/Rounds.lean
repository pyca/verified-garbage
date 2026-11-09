module

public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-CBC: the contracts on the key schedule they are given

Not trusted: the contracts that the proofs of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` are written against,
for the key schedule and the number of rounds they are given, whatever key
that schedule came from. The shared contracts in `Spec/` are stated for
every AES key whose schedule is in memory with its number of rounds
(`Spec.Aes.KeySchedule`), and follow from these (`Verified.post_mono`): with
the schedule of a key and its rounds, the cipher of the schedule is AES with
that key.
-/

@[expose] public section

namespace VG.Proof.AesCbc

open VG.Spec
open VG.Spec.Cbc

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CBC encryption (§6.2) by AES with `w`, from the chaining value
at `iv`, and the chaining value with the last ciphertext block (unchanged
if `n = 0`). -/
def encryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := encrypt ciph (Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CBC decryption (§6.2) by AES with `w`, from the chaining value
at `iv`, and the chaining value with the last ciphertext block, the last
block at `data` on entry (unchanged if `n = 0`). -/
def decryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciphInv := aesInvWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := blocksAt m data n.toNat
      blocksAt m' data n.toNat = decrypt ciphInv (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-! ## The contracts without `scratch`'s clause

`Spec.Cbc.aesEncryptContract` and `Spec.Cbc.aesDecryptContract` are these
postconditions and `scratch` left scrubbed (`Wipe.scrubbedPost`,
`Wipe.encrypt_eq`, `Wipe.decrypt_eq`). -/

namespace Wipe

/-- The precondition of every CBC function. -/
def pre (pb : Nat) : Curry (aesSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _scratch _ => rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- The postcondition of `Spec.Cbc.aesEncryptContract` without its clause on
`scratch`. -/
def encPost (pb : Nat) : aesSig.Post pb := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Aes.KeySchedule m schedule rounds.toNat key →
    let ciph := aes key
    let cs := encrypt ciph (Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
    blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs

/-- The postcondition of `Spec.Cbc.aesDecryptContract` without its clause on
`scratch`. -/
def decPost (pb : Nat) : aesSig.Post pb := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Aes.KeySchedule m schedule rounds.toNat key →
    let ciphInv := aesInv key
    let cs := blocksAt m data n.toNat
    blocksAt m' data n.toNat = decrypt ciphInv (Aes.bytesAt m iv 16) cs ∧
      Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs

end Wipe

/-- `Spec.Cbc.aesEncryptContract` without `scratch`'s clause, from
`encryptRoundsContract`. -/
theorem encrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (encryptRoundsContract A stack)) :
    Verified T c (aesSig.contract A (Wipe.pre A.ptrBits) (Wipe.encPost A.ptrBits) false stack none) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cbc.aesDecryptContract` without `scratch`'s clause, from
`decryptRoundsContract`. -/
theorem decrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (decryptRoundsContract A stack)) :
    Verified T c (aesSig.contract A (Wipe.pre A.ptrBits) (Wipe.decPost A.ptrBits) false stack none) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

end VG.Proof.AesCbc
