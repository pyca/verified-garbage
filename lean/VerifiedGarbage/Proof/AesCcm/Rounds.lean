module

public import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-CCM: the contracts on the key schedule they are given

Not trusted: the contracts that the proofs of `vg_aes_ccm_seal` and
`vg_aes_ccm_open` are written against, for the cipher of the key schedule
and the number of rounds they are given (`Spec.Ccm.ctxCiph`), whatever key
that schedule came from. The shared contracts in `Spec/` are stated for
every AES key whose schedule is in memory with its number of rounds
(`Spec.Aes.KeySchedule`), and follow from these (`Verified.post_mono`): with
the schedule of a key and its rounds, the cipher of the schedule is AES with
that key (`Spec.Ccm.ctxCiph_eq`).
-/

@[expose] public section

namespace VG.Proof.AesCcm

open VG.Spec
open VG.Spec.Ccm

/-- For `rounds` of 10, 12 or 14, with the key schedule in the first
`16 (rounds + 1)` bytes at `schedule`: the `len` bytes at `data` are
encrypted, with the nonce at `nonce` and the `aad_len` bytes of associated
data at `aad` (`encryptWith`), and the encrypted MAC of `tag_len` bytes is
at `tag`. -/
def sealRoundsPost (pb : Nat) : sealSig.Post pb :=
  fun schedule rounds nonce nonceLen aad aadLen data len tag tagLen m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m schedule rounds.toNat) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag tagLen.toNat)

/-- For `rounds` of 10, 12 or 14, a MAC length `tag_len`, a nonce of
`nonce_len` bytes and `len` bytes of payload that Appendix A.1 allows, with
the key schedule in the first `16 (rounds + 1)` bytes at `schedule`:
encrypts the `len` bytes at `data` in place, with the nonce at `nonce` and
the `aad_len` bytes of associated data at `aad` (`encryptWith`), and writes
the encrypted MAC of `tag_len` bytes to `tag`. -/
def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule in the first
`16 (rounds + 1)` bytes at `schedule` and the received tag (the encrypted
MAC) the `tag_len` bytes at `tag`: if the MAC is right for the `len` bytes of
encrypted payload at `data`, the nonce at `nonce` and the `aad_len` bytes of
associated data at `aad` (`decryptWith`), the result is 1 and the payload is
at `data`; otherwise the result is 0 and zeros are at `data`. -/
def openRoundsPost (pb : Nat) : openSig.Post pb :=
  fun schedule rounds nonce nonceLen aad aadLen data len tag tagLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match decryptWith (ctxCiph m schedule rounds.toNat) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- For `rounds` of 10, 12 or 14, a MAC length `tag_len`, a nonce of
`nonce_len` bytes and `len` bytes of payload that Appendix A.1 allows, with
the key schedule in the first `16 (rounds + 1)` bytes at `schedule` and the
received tag (the encrypted MAC) the `tag_len` bytes at `tag`: if the MAC is
right for the `len` bytes of encrypted payload at `data`, the nonce at
`nonce` and the `aad_len` bytes of associated data at `aad` (`decryptWith`),
returns 1 and leaves the payload at `data`; otherwise returns 0 and leaves
zeros at `data`. May leak which (`decryptWith`'s outcome). -/
def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

theorem rounds_of_keySchedule {mem : Mem} {p : Addr} {r : Nat} {key : List Byte}
    (h : Spec.Aes.KeySchedule mem p r key) : r = 10 ∨ r = 12 ∨ r = 14 := by
  obtain ⟨hl, hr, -⟩ := h
  rw [hr]
  rcases hl with h | h | h <;> rw [h] <;> decide

/-- `Spec.Ccm.sealContract` from `sealRoundsContract`. -/
theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (Spec.Ccm.sealContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ _ _ _ _ hp key hk => by
    dsimp only [sealRoundsPost, Spec.Ccm.sealPost] at hp ⊢
    have h' := hp (rounds_of_keySchedule hk)
    obtain ⟨-, hr, hw⟩ := hk
    rw [hr] at hw h'
    rw [ctxCiph_eq hw] at h'
    exact h'

/-- `Spec.Ccm.openContract` from `openRoundsContract`. -/
theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (Spec.Ccm.openContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ _ _ _ _ hp key hk => by
    dsimp only [openRoundsPost, Spec.Ccm.openPost] at hp ⊢
    have h' := hp (rounds_of_keySchedule hk)
    obtain ⟨-, hr, hw⟩ := hk
    rw [hr] at hw h'
    rw [ctxCiph_eq hw] at h'
    exact h'

end VG.Proof.AesCcm
