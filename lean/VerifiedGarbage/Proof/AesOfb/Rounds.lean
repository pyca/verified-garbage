module

public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-OFB: the contract on the key schedule it is given

Not trusted: the contracts that the proofs of `vg_aes_ofb` are written against,
for the key schedule and the number of rounds they are given, whatever key
that schedule came from. The shared contracts in `Spec/` are stated for
every AES key whose schedule is in memory with its number of rounds
(`Spec.Aes.KeySchedule`), and follow from these (`Verified.post_mono`): with
the schedule of a key and its rounds, the cipher of the schedule is AES with
that key.
-/

@[expose] public section

namespace VG.Proof.AesOfb

open VG.Spec
open VG.Spec.Ofb

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their OFB encryption or decryption (§6.4) by AES with `w`, from the
block at `iv`, and that block with the last output block `Oₙ` (unchanged
if `n = 0`). -/
def roundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Cbc.blocksAt m' data n.toNat = crypt ciph (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' iv 16 = next ciph (Aes.bytesAt m iv 16) n.toNat)
    (stack := stack)

/-- `Spec.Ofb.aesContract` from `roundsContract`. -/
theorem keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (roundsContract A stack)) : Verified T c (Spec.Ofb.aesContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

end VG.Proof.AesOfb
