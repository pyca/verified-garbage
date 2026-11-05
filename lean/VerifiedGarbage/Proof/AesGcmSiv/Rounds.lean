module

public import VerifiedGarbage.Spec.GcmSiv.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-GCM-SIV: the contracts on the key schedule they are given

Not trusted: the contracts that the proofs of `vg_aes_gcm_siv_seal` and
`vg_aes_gcm_siv_open` are written against, for the cipher of the key
schedule and the number of rounds they are given (`Spec.GcmSiv.ctxCiph`,
`Spec.GcmSiv.keyLen`), whatever key that schedule came from. The shared
contracts in `Spec/` are stated for every key-generating key whose schedule
is in memory with its number of rounds (`Spec.Aes.KeySchedule`), and follow
from these (`Verified.post_mono`): with the schedule of a key and its
rounds, the cipher of the schedule is AES with that key
(`Spec.GcmSiv.ctxCiph_eq`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv

open VG.Spec
open VG.Spec.GcmSiv

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule`: the `len` bytes at
`data` are encrypted, with the 12-byte nonce at `nonce` and the `aad_len`
bytes of additional data at `aad` (`encryptWith`), and the 16-byte tag is
at `tag`. -/
def sealRoundsPost (pb : Nat) : sealSig.Post pb :=
  fun schedule rounds nonce aad aadLen data len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat) (Aes.bytesAt m nonce 12)
        (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule`: encrypts the `len` bytes
at `data` in place, with the 12-byte nonce at `nonce` and the `aad_len`
bytes of additional data at `aad` (`encryptWith`), and writes the 16-byte
tag to `tag`. -/
def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule` and the received tag the
16 bytes at `tag`: if the tag is right for the `len` bytes of encrypted
plaintext at `data`, the 12-byte nonce at `nonce` and the `aad_len` bytes of
additional data at `aad` (`decryptWith`), the result is 1 and the plaintext
is at `data`; otherwise the result is 0 and zeros are at `data`. -/
def openRoundsPost (pb : Nat) : openSig.Post pb :=
  fun schedule rounds nonce aad aadLen data len tag m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 14) →
    match decryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat)
        (Aes.bytesAt m nonce 12) (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat)
        (Aes.bytesAt m tag 16) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule` and the received tag the
16 bytes at `tag`: if the tag is right for the `len` bytes of encrypted
plaintext at `data`, the 12-byte nonce at `nonce` and the `aad_len` bytes of
additional data at `aad` (`decryptWith`), returns 1 and leaves the plaintext
at `data`; otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- `Spec.GcmSiv.sealContract` from `sealRoundsContract`. -/
theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (Spec.GcmSiv.sealContract A stack) :=
  h.post_mono fun schedule rounds _ _ _ _ _ _ m _ _ hp key hl hk => by
    dsimp only [sealRoundsPost, Spec.GcmSiv.sealPost] at hp ⊢
    have hr : rounds.toNat = Aes.rounds (key.length / 4) := hk.2.1
    have hw := hk.2.2
    have hn : keyLen (Aes.rounds (key.length / 4)) = key.length := by
      rcases hl with h | h <;> rw [h] <;> rfl
    have e : encryptWith (aes key) key.length =
        encryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat) := by
      rw [hr] at hw ⊢
      rw [ctxCiph_eq hw, hn]
    have g : rounds.toNat = 10 ∨ rounds.toNat = 14 := by
      rw [hr]; rcases hl with h | h <;> rw [h] <;> decide
    have h' := hp g
    rw [e]
    exact h'

/-- `Spec.GcmSiv.openContract` from `openRoundsContract`. -/
theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (Spec.GcmSiv.openContract A stack) :=
  h.post_mono fun schedule rounds _ _ _ _ _ _ m _ _ hp key hl hk => by
    dsimp only [openRoundsPost, Spec.GcmSiv.openPost] at hp ⊢
    have hr : rounds.toNat = Aes.rounds (key.length / 4) := hk.2.1
    have hw := hk.2.2
    have hn : keyLen (Aes.rounds (key.length / 4)) = key.length := by
      rcases hl with h | h <;> rw [h] <;> rfl
    have e : decryptWith (aes key) key.length =
        decryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat) := by
      rw [hr] at hw ⊢
      rw [ctxCiph_eq hw, hn]
    have g : rounds.toNat = 10 ∨ rounds.toNat = 14 := by
      rw [hr]; rcases hl with h | h <;> rw [h] <;> decide
    have h' := hp g
    rw [e]
    split
    all_goals
      rename_i heq
      rw [heq] at h'
      exact h'

end VG.Proof.AesGcmSiv
