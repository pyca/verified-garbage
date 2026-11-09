module

public import VerifiedGarbage.Spec.Siv.Contract
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-SIV: the contracts on the key context and the number of rounds they are given

Not trusted: the contracts that the proofs of `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` are written against, for
the ciphers of the key context for the number of rounds they are given
(`Spec.Siv.ctxMac`, `Spec.Siv.ctxCiph`), whatever key the context came from. The shared contracts in
`Spec/` are stated for every key whose context is in memory with its number
of rounds (`Spec.Siv.KeyRounds`), and follow from these
(`Verified.post_mono`).
-/

@[expose] public section

namespace VG.Proof.AesSiv

open VG.Spec
open VG.Spec.Siv

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
components of associated data `ads` lists (`components`): the `len` bytes of
plaintext at `data` are encrypted (`encryptWith`), and the synthetic IV `V`
is the 16 bytes at `siv`. -/
def encryptRoundsPost (pb : Nat) : encryptSig.Post pb :=
  fun ctx rounds ads adsCount data len siv m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
        (components pb m ads adsCount.toNat) (Aes.bytesAt m data len.toNat) =
      (Aes.bytesAt m' siv 16, Aes.bytesAt m' data len.toNat)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
components of associated data `ads` lists (`components`): encrypts the `len`
bytes of plaintext at `data` in place (`encryptWith`) and writes the
synthetic IV `V` to `siv`. -/
def encryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptSig.contract A (pre := encryptPre A.ptrBits) (post := encryptRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the
components of associated data `ads` lists and the received synthetic IV `V`
the 16 bytes at `siv`: if `V` is right for the plaintext of the `len` bytes
of ciphertext at `data` (`decryptWith`), the result is 1 and the plaintext is
at `data`; otherwise the result is 0 and zeros are at `data`. -/
def decryptRoundsPost (pb : Nat) : decryptSig.Post pb :=
  fun ctx rounds ads adsCount data len siv m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
        (components pb m ads adsCount.toNat) (Aes.bytesAt m siv 16)
        (Aes.bytesAt m data len.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the
components of associated data `ads` lists and the received synthetic IV `V`
the 16 bytes at `siv`: if `V` is right for the plaintext of the `len` bytes
of ciphertext at `data` (`decryptWith`), returns 1 and leaves the plaintext
at `data`; otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def decryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptSig.contract A (pre := decryptPre A.ptrBits) (post := decryptRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (decryptLeak A.ptrBits))

/-- What the key context of a key holds, with the key's number of rounds:
CMAC under `K1` and AES under `K2`, for 10, 12 or 14 rounds. -/
theorem keyRounds_ctx {m : Mem} {ctx : Addr} {r : Nat} {key : List Byte}
    (h : Spec.Siv.KeyRounds m ctx r key) :
    ctxMac m ctx r = cmac (key.take (key.length / 2)) ∧
      ctxCiph m ctx r = Cmac.aes (key.drop (key.length / 2)) ∧ (r = 10 ∨ r = 12 ∨ r = 14) := by
  obtain ⟨hr, hk⟩ := h
  subst hr
  refine ⟨ctxMac_eq hk, ctxCiph_eq hk, ?_⟩
  rcases hk.1 with h | h | h <;> rw [h] <;> decide

/-- `Spec.Siv.encryptContract` from `encryptRoundsContract`. -/
theorem encrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (encryptRoundsContract A stack)) : Verified T c (Spec.Siv.encryptContract A stack) :=
  h.post_mono fun ctx rounds _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [encryptRoundsPost, Spec.Siv.encryptPost] at hp ⊢
    obtain ⟨hm, hc, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hm, hc] at h'
    exact h'

/-- `Spec.Siv.decryptContract` from `decryptRoundsContract`. -/
theorem decrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (decryptRoundsContract A stack)) : Verified T c (Spec.Siv.decryptContract A stack) :=
  h.post_mono fun ctx rounds _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [decryptRoundsPost, Spec.Siv.decryptPost] at hp ⊢
    obtain ⟨hm, hc, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hm, hc] at h'
    split
    all_goals
      rename_i heq
      rw [heq] at h'
      exact h'

end VG.Proof.AesSiv
