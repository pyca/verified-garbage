module

public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-OCB: the contracts on the key context and the number of rounds they are given

Not trusted: the contracts that the proofs of `vg_aes_ocb_seal` and `vg_aes_ocb_open` are written against, for
the ciphers of the key context for the number of rounds they are given
(`Spec.Ocb.ctxCiph`, `Spec.Ocb.ctxInv`, `Spec.Ocb.ctxLstar`), whatever key the context came from. The shared contracts in
`Spec/` are stated for every key whose context is in memory with its number
of rounds (`Spec.Ocb.KeyRounds`), and follow from these
(`Verified.post_mono`).
-/

@[expose] public section

namespace VG.Proof.AesOcb

open VG.Spec
open VG.Spec.Ocb

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: the `len`
bytes at `data` are encrypted, with the nonce at `nonce` and the `aad_len`
bytes of associated data at `aad` (`encryptWith`), and the tag of `tag_len`
bytes is at `tag`. -/
def sealRoundsPost (pb : Nat) : sealSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxLstar m ctx) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m aad aadLen.toNat)
        (Aes.bytesAt m data len.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag tagLen.toNat)

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx`: encrypts the `len` bytes at `data`
in place, with the nonce at `nonce` and the `aad_len` bytes of associated
data at `aad` (`encryptWith`), and writes the tag of `tag_len` bytes to
`tag`. -/
def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if the tag is right for the `len`
bytes of encrypted data at `data`, the nonce at `nonce` and the `aad_len`
bytes of associated data at `aad` (`decryptWith`), the result is 1 and the
plaintext is at `data`; otherwise the result is 0 and zeros are at
`data`. -/
def openRoundsPost (pb : Nat) : openSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match decryptWith (ctxCiph m ctx rounds.toNat) (ctxInv m ctx rounds.toNat)
        (ctxLstar m ctx) tagLen.toNat (Aes.bytesAt m nonce nonceLen.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx` and the received tag the `tag_len`
bytes at `tag`: if the tag is right for the `len` bytes of encrypted data at
`data`, the nonce at `nonce` and the `aad_len` bytes of associated data at
`aad` (`decryptWith`), returns 1 and leaves the plaintext at `data`;
otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- What the key context of a key holds, with the key's number of rounds:
the key's ciphers and `L_*`, for 10, 12 or 14 rounds. -/
theorem keyRounds_ctx {m : Mem} {ctx : Addr} {r : Nat} {key : List Byte}
    (h : Spec.Ocb.KeyRounds m ctx r key) :
    ctxCiph m ctx r = aes key ∧ ctxInv m ctx r = aesInv key ∧ ctxLstar m ctx = aes key 0 ∧
      (r = 10 ∨ r = 12 ∨ r = 14) := by
  obtain ⟨hl, hr, hk⟩ := h
  subst hr
  refine ⟨by unfold ctxCiph; rw [hk.1]; rfl, by unfold ctxInv; rw [hk.1]; rfl, hk.2, ?_⟩
  rcases hl with h | h | h <;> rw [h] <;> decide

/-- `Spec.Ocb.sealContract` from `sealRoundsContract`. -/
theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (Spec.Ocb.sealContract A stack) :=
  h.post_mono fun ctx rounds _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [sealRoundsPost, Spec.Ocb.sealPost] at hp ⊢
    obtain ⟨hc, hi, hs, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hs] at h'
    exact h'

/-- `Spec.Ocb.openContract` from `openRoundsContract`. -/
theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (Spec.Ocb.openContract A stack) :=
  h.post_mono fun ctx rounds _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [openRoundsPost, Spec.Ocb.openPost] at hp ⊢
    obtain ⟨hc, hi, hs, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hi, hs] at h'
    split
    all_goals
      rename_i heq
      rw [heq] at h'
      exact h'

end VG.Proof.AesOcb
