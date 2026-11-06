module

public import VerifiedGarbage.Spec.Gcm.Powers8
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# AES-GCM: the contracts on the key context and the number of rounds they are given

Not trusted: the contracts that the proofs of AES-GCM's functions that read a
key context with a number of rounds are written against, for the cipher of
the context's key schedule for the number of rounds they are given
(`Spec.Gcm.ctxCiph`) and its hash subkey (`Spec.Gcm.ctxH`), whatever key the
context came from. The shared contracts in `Spec/` are stated for every key
whose context is in memory with its number of rounds (`Spec.Gcm.KeyRounds`),
and follow from these (`Verified.post_mono`): with the context of a key and
its rounds, the context's cipher and hash subkey are the key's
(`keyRounds_ctx`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec
open VG.Spec.Gcm

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: the `len`
bytes at `data` are encrypted, with the IV the `nonce_len` bytes at `nonce`
and the `aad_len` bytes of additional data at `aad` (GCM-AE, `encryptWith`),
and the 16-byte tag is at `tag`. -/
def sealRoundsPost (pb : Nat) : sealSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16 (Aes.bytesAt m nonce nonceLen.toNat)
        (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: encrypts the
`len` bytes at `data` in place, with the IV the `nonce_len` bytes at `nonce`
and the `aad_len` bytes of additional data at `aad` (GCM-AE, `encryptWith`),
and writes the 16-byte tag to `tag`. -/
def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if `tag_len` is a tag length
`tagLenOk` allows and the tag is that of the `len` bytes of ciphertext at
`data` and the `aad_len` bytes of additional data at `aad`, with the IV the
`nonce_len` bytes at `nonce` (GCM-AD, `decryptWith`), the result is 1 and
the plaintext is at `data`; otherwise the result is 0 and the bytes at
`data` are as they were. -/
def openRoundsPost (pb : Nat) : openSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = Aes.bytesAt m data len.toNat

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if `tag_len` is a
supported tag length and the tag is that of the `len` bytes of ciphertext
at `data` and the `aad_len` bytes of additional data at `aad`, with the IV
the `nonce_len` bytes at `nonce` (GCM-AD, `decryptWith`), returns 1 and
leaves the plaintext at `data`; otherwise returns 0 and leaves the bytes at
`data` as they were. May leak which (`openResult`'s outcome). -/
def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext of a plaintext
`p` of exactly `text_len` bytes (and `aad_len` modulo 2⁶⁴) so far, then afterwards it
represents the message with the ciphertext of `p` followed by the `len`
bytes at `data`, whose encryption is written to `data`: the last `len`
bytes of `GCTR_K(inc₃₂(J₀), p ‖ data)`. -/
def streamEncryptRoundsPost (pb : Nat) : streamCryptSig.Post pb :=
  fun ctx rounds state aadLen textLen data len m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a p, StreamRepr m state ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ Aes.bytesAt m data len.toNat)
      StreamRepr m' state ciph h iv a c ∧ Aes.bytesAt m' data len.toNat = c.drop p.length

/-- For `rounds` of 10, 12 or 14 (`streamTextPre`): `streamEncryptRoundsPost`. -/
def streamEncryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A (pre := streamTextPre A.ptrBits) (post := streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext `c` of `text_len`
bytes (exactly, and `aad_len` modulo 2⁶⁴) so far, then afterwards it represents the message
with the ciphertext `c` followed by the `len` bytes at `data`, whose
decryption is written to `data`: the last `len` bytes of
`GCTR_K(inc₃₂(J₀), c ‖ data)`. -/
def streamDecryptRoundsPost (pb : Nat) : streamCryptSig.Post pb :=
  fun ctx rounds state aadLen textLen data len m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a c, StreamRepr m state ciph h iv a c →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
      let c' := c ++ Aes.bytesAt m data len.toNat
      StreamRepr m' state ciph h iv a c' ∧
        Aes.bytesAt m' data len.toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length

/-- For `rounds` of 10, 12 or 14 (`streamTextPre`): `streamDecryptRoundsPost`. -/
def streamDecryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A (pre := streamTextPre A.ptrBits) (post := streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext `c` of `text_len`
bytes (exactly, and `aad_len` modulo 2⁶⁴), its 16-byte tag (`fullTag`) is
at `tag`. -/
def streamFinishRoundsPost (pb : Nat) : streamFinishSig.Post pb :=
  fun ctx rounds state aadLen textLen tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a c, StreamRepr m state ciph h iv a c →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
      Aes.bytesAt m' tag 16 = fullTag ciph h iv a c

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext `c` of `text_len`
bytes (exactly, and `aad_len` modulo 2⁶⁴), writes its 16-byte tag
(`fullTag`) to `tag`. -/
def streamFinishRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishSig.contract A (pre := streamFinishPre A.ptrBits) (post := streamFinishRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if the streaming state at
`state` represents a message with the IV `iv`, additional data `a` of
`aad_len` bytes and the ciphertext `c` of `text_len` bytes (both modulo
2⁶⁴), and `T` is its 16-byte tag (`fullTag`): the result is 1 if `tag_len`
is a supported length and the received tag is the first `tag_len`
bytes of `T` (§7.2 step 8), and 0 otherwise. -/
def streamVerifyRoundsPost (pb : Nat) : streamVerifySig.Post pb :=
  fun ctx rounds state aadLen textLen tag tagLen m _ r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a c, StreamRepr m state ciph h iv a c →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tagLen.toNat ∧ t.take tagLen.toNat = Aes.bytesAt m tag tagLen.toNat then r = 1
      else r = 0

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if the streaming state at
`state` represents a message with the IV `iv`, additional data `a` of
`aad_len` bytes and the ciphertext `c` of `text_len` bytes (both modulo
2⁶⁴), and `T` is its 16-byte tag (`fullTag`): returns 1 if `tag_len` is a
supported length and the received tag is the first `tag_len` bytes of
`T` (§7.2 step 8), and 0 otherwise. -/
def streamVerifyRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifySig.contract A (pre := streamVerifyPre A.ptrBits) (post := streamVerifyRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, and slices
of `len` bytes in all listed by `src`: the `len` bytes at `dst` are the
encryption of their concatenation (`gathered`), with the IV the `nonce_len`
bytes at `nonce` and the `aad_len` bytes of additional data at `aad`
(GCM-AE, `encryptWith`), and the 16-byte tag is at `tag`. (`sealRoundsPost`, with
the plaintext gathered from `src` and the ciphertext written to `dst`.) -/
def sealGatherRoundsPost (pb : Nat) : sealGatherSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    gatheredLen pb m src srcCount.toNat = len.toNat →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16 (Aes.bytesAt m nonce nonceLen.toNat)
        (gathered pb m src srcCount.toNat) (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' dst len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10, 12 or 14 and slices of `len` bytes in all
(`sealGatherPre`): `sealGatherRoundsPost`. -/
def sealGatherRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherSig.contract A (pre := sealGatherPre A.ptrBits) (post := sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `sealGatherRoundsContract`, with the larger key context. -/
def sealGatherPrecomputedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrecomputedSig.contract A (pre := sealGatherPrecomputedPre A.ptrBits)
    (post := sealGatherRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `sealRoundsPost`, with the larger key context. -/
def sealPrecomputedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrecomputedSig.contract A (pre := sealPrecomputedPre A.ptrBits)
    (post := sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `openRoundsPost`, with the larger key context; it may leak what `openRoundsContract`
may (`openLeak`). -/
def openPrecomputedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrecomputedSig.contract A (pre := openPrecomputedPre A.ptrBits)
    (post := openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- `streamEncryptRoundsPost`, with the larger key context. -/
def streamEncryptPrecomputedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamTextPrecomputedPre A.ptrBits)
    (post := streamEncryptRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `streamDecryptRoundsPost`, with the larger key context. -/
def streamDecryptPrecomputedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamTextPrecomputedPre A.ptrBits)
    (post := streamDecryptRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- The unchanged `sealRoundsContract` postcondition with prepared powers. -/
def sealPreparedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPreparedPre A.ptrBits)
    (post := sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `openRoundsContract` postcondition with prepared powers. -/
def openPreparedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPreparedPre A.ptrBits)
    (post := openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- The unchanged `streamEncryptRoundsContract` postcondition with prepared powers. -/
def streamEncryptPreparedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `streamDecryptRoundsContract` postcondition with prepared powers. -/
def streamDecryptPreparedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `sealGatherRoundsContract` postcondition with prepared powers. -/
def sealGatherPreparedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPreparedPre A.ptrBits)
    (post := sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `sealRoundsContract` postcondition with 16 prepared powers. -/
def sealPrepared16RoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPrepared16Pre A.ptrBits)
    (post := sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `openRoundsContract` postcondition with 16 prepared powers. -/
def openPrepared16RoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPrepared16Pre A.ptrBits)
    (post := openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- The unchanged `streamEncryptRoundsContract` postcondition with 16 prepared powers. -/
def streamEncryptPrepared16RoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPrepared16Pre A.ptrBits)
    (post := streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `streamDecryptRoundsContract` postcondition with 16 prepared powers. -/
def streamDecryptPrepared16RoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPrepared16Pre A.ptrBits)
    (post := streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `sealGatherRoundsContract` postcondition with 16 prepared powers. -/
def sealGatherPrepared16RoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPrepared16Pre A.ptrBits)
    (post := sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `sealRoundsPost`, which does not depend on `pw`. -/
def sealWithPowersRoundsPost (pb : Nat) : sealWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag _pw m m' r =>
    sealRoundsPost pb ctx rounds nonce nonceLen aad aadLen data len tag m m' r

/-- `sealWithPowersPre` and `sealWithPowersRoundsPost`. -/
def sealWithPowersRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealWithPowersSig.contract A (pre := sealWithPowersPre A.ptrBits)
    (post := sealWithPowersRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `openRoundsPost`, which does not depend on `pw`. -/
def openWithPowersRoundsPost (pb : Nat) : openWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw m m' r =>
    openRoundsPost pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r

/-- `openWithPowersPre`, `openWithPowersRoundsPost`, and what `openRoundsContract` may
leak (`openWithPowersLeak`). -/
def openWithPowersRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openWithPowersSig.contract A (pre := openWithPowersPre A.ptrBits)
    (post := openWithPowersRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openWithPowersLeak A.ptrBits))


/-- What the key context of a key holds, with the key's number of rounds:
the key's cipher and hash subkey, for 10, 12 or 14 rounds. -/
theorem keyRounds_ctx {m : Mem} {ctx : Addr} {r : Nat} {key : List Byte}
    (h : Spec.Gcm.KeyRounds m ctx r key) :
    ctxCiph m ctx r = aes key ∧ ctxH m ctx = aes key 0 ∧ (r = 10 ∨ r = 12 ∨ r = 14) := by
  obtain ⟨hl, hr, hk⟩ := h
  subst hr
  refine ⟨by unfold ctxCiph; rw [hk.1]; rfl, hk.2, ?_⟩
  rcases hl with h | h | h <;> rw [h] <;> decide

theorem sealPost_imp (pb : Nat) : sealSig.PostImp pb (sealRoundsPost pb) (Spec.Gcm.sealPost pb) :=
  fun ctx rounds _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [sealRoundsPost, Spec.Gcm.sealPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh, ← encrypt_eq] at h'
    exact h'

theorem sealGatherPost_imp (pb : Nat) : sealGatherSig.PostImp pb (sealGatherRoundsPost pb) (Spec.Gcm.sealGatherPost pb) :=
  fun ctx rounds _ _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [sealGatherRoundsPost, Spec.Gcm.sealGatherPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh, ← encrypt_eq] at h'
    exact h'

theorem openPost_imp (pb : Nat) : openSig.PostImp pb (openRoundsPost pb) (Spec.Gcm.openPost pb) :=
  fun ctx rounds _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [openRoundsPost, Spec.Gcm.openPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh] at h'
    split
    all_goals
      rename_i heq
      rw [heq] at h'
      exact h'

theorem streamEncryptPost_imp (pb : Nat) : streamCryptSig.PostImp pb (streamEncryptRoundsPost pb) (Spec.Gcm.streamEncryptPost pb) :=
  fun ctx rounds _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [streamEncryptRoundsPost, Spec.Gcm.streamEncryptPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh] at h'
    exact h'

theorem streamDecryptPost_imp (pb : Nat) : streamCryptSig.PostImp pb (streamDecryptRoundsPost pb) (Spec.Gcm.streamDecryptPost pb) :=
  fun ctx rounds _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [streamDecryptRoundsPost, Spec.Gcm.streamDecryptPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh] at h'
    exact h'

theorem streamFinishPost_imp (pb : Nat) : streamFinishSig.PostImp pb (streamFinishRoundsPost pb) (Spec.Gcm.streamFinishPost pb) :=
  fun ctx rounds _ _ _ _ m _ _ hp key hk => by
    dsimp only [streamFinishRoundsPost, Spec.Gcm.streamFinishPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh] at h'
    exact h'

theorem streamVerifyPost_imp (pb : Nat) : streamVerifySig.PostImp pb (streamVerifyRoundsPost pb) (Spec.Gcm.streamVerifyPost pb) :=
  fun ctx rounds _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [streamVerifyRoundsPost, Spec.Gcm.streamVerifyPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh] at h'
    exact h'

theorem sealWithPowersPost_imp (pb : Nat) :
    sealWithPowersSig.PostImp pb (sealWithPowersRoundsPost pb) (Spec.Gcm.sealWithPowersPost pb) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag _ m m' r hp =>
    sealPost_imp pb ctx rounds nonce nonceLen aad aadLen data len tag m m' r hp

theorem openWithPowersPost_imp (pb : Nat) :
    openWithPowersSig.PostImp pb (openWithPowersRoundsPost pb) (Spec.Gcm.openWithPowersPost pb) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _ m m' r hp =>
    openPost_imp pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r hp

/-- `Spec.Gcm.openContract` from `openRoundsContract`. -/
theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (Spec.Gcm.openContract A stack) :=
  h.post_mono (openPost_imp _)

/-- `Spec.Gcm.openPrecomputedContract` from `openPrecomputedRoundsContract`. -/
theorem openPrecomputed_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openPrecomputedRoundsContract A stack)) : Verified T c (Spec.Gcm.openPrecomputedContract A stack) :=
  h.post_mono (openPost_imp _)

/-- `Spec.Gcm.openPrepared16Contract` from `openPrepared16RoundsContract`. -/
theorem openPrepared16_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openPrepared16RoundsContract A stack)) : Verified T c (Spec.Gcm.openPrepared16Contract A stack) :=
  h.post_mono (openPost_imp _)

/-- `Spec.Gcm.openPreparedContract` from `openPreparedRoundsContract`. -/
theorem openPrepared_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openPreparedRoundsContract A stack)) : Verified T c (Spec.Gcm.openPreparedContract A stack) :=
  h.post_mono (openPost_imp _)

/-- `Spec.Gcm.openWithPowersContract` from `openWithPowersRoundsContract`. -/
theorem openWithPowers_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openWithPowersRoundsContract A stack)) : Verified T c (Spec.Gcm.openWithPowersContract A stack) :=
  h.post_mono (openWithPowersPost_imp _)

/-- `Spec.Gcm.sealContract` from `sealRoundsContract`. -/
theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (Spec.Gcm.sealContract A stack) :=
  h.post_mono (sealPost_imp _)

/-- `Spec.Gcm.sealGatherContract` from `sealGatherRoundsContract`. -/
theorem sealGather_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherRoundsContract A stack)) : Verified T c (Spec.Gcm.sealGatherContract A stack) :=
  h.post_mono (sealGatherPost_imp _)

/-- `Spec.Gcm.sealGatherPrecomputedContract` from `sealGatherPrecomputedRoundsContract`. -/
theorem sealGatherPrecomputed_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherPrecomputedRoundsContract A stack)) : Verified T c (Spec.Gcm.sealGatherPrecomputedContract A stack) :=
  h.post_mono (sealGatherPost_imp _)

/-- `Spec.Gcm.sealGatherPrepared16Contract` from `sealGatherPrepared16RoundsContract`. -/
theorem sealGatherPrepared16_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherPrepared16RoundsContract A stack)) : Verified T c (Spec.Gcm.sealGatherPrepared16Contract A stack) :=
  h.post_mono (sealGatherPost_imp _)

/-- `Spec.Gcm.sealGatherPreparedContract` from `sealGatherPreparedRoundsContract`. -/
theorem sealGatherPrepared_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherPreparedRoundsContract A stack)) : Verified T c (Spec.Gcm.sealGatherPreparedContract A stack) :=
  h.post_mono (sealGatherPost_imp _)

/-- `Spec.Gcm.sealPrecomputedContract` from `sealPrecomputedRoundsContract`. -/
theorem sealPrecomputed_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealPrecomputedRoundsContract A stack)) : Verified T c (Spec.Gcm.sealPrecomputedContract A stack) :=
  h.post_mono (sealPost_imp _)

/-- `Spec.Gcm.sealPrepared16Contract` from `sealPrepared16RoundsContract`. -/
theorem sealPrepared16_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealPrepared16RoundsContract A stack)) : Verified T c (Spec.Gcm.sealPrepared16Contract A stack) :=
  h.post_mono (sealPost_imp _)

/-- `Spec.Gcm.sealPreparedContract` from `sealPreparedRoundsContract`. -/
theorem sealPrepared_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealPreparedRoundsContract A stack)) : Verified T c (Spec.Gcm.sealPreparedContract A stack) :=
  h.post_mono (sealPost_imp _)

/-- `Spec.Gcm.sealWithPowersContract` from `sealWithPowersRoundsContract`. -/
theorem sealWithPowers_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealWithPowersRoundsContract A stack)) : Verified T c (Spec.Gcm.sealWithPowersContract A stack) :=
  h.post_mono (sealWithPowersPost_imp _)

/-- `Spec.Gcm.streamDecryptContract` from `streamDecryptRoundsContract`. -/
theorem streamDecrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptRoundsContract A stack)) : Verified T c (Spec.Gcm.streamDecryptContract A stack) :=
  h.post_mono (streamDecryptPost_imp _)

/-- `Spec.Gcm.streamDecryptPrecomputedContract` from `streamDecryptPrecomputedRoundsContract`. -/
theorem streamDecryptPrecomputed_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptPrecomputedRoundsContract A stack)) : Verified T c (Spec.Gcm.streamDecryptPrecomputedContract A stack) :=
  h.post_mono (streamDecryptPost_imp _)

/-- `Spec.Gcm.streamDecryptPrepared16Contract` from `streamDecryptPrepared16RoundsContract`. -/
theorem streamDecryptPrepared16_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptPrepared16RoundsContract A stack)) : Verified T c (Spec.Gcm.streamDecryptPrepared16Contract A stack) :=
  h.post_mono (streamDecryptPost_imp _)

/-- `Spec.Gcm.streamDecryptPreparedContract` from `streamDecryptPreparedRoundsContract`. -/
theorem streamDecryptPrepared_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptPreparedRoundsContract A stack)) : Verified T c (Spec.Gcm.streamDecryptPreparedContract A stack) :=
  h.post_mono (streamDecryptPost_imp _)

/-- `Spec.Gcm.streamEncryptContract` from `streamEncryptRoundsContract`. -/
theorem streamEncrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptRoundsContract A stack)) : Verified T c (Spec.Gcm.streamEncryptContract A stack) :=
  h.post_mono (streamEncryptPost_imp _)

/-- `Spec.Gcm.streamEncryptPrecomputedContract` from `streamEncryptPrecomputedRoundsContract`. -/
theorem streamEncryptPrecomputed_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptPrecomputedRoundsContract A stack)) : Verified T c (Spec.Gcm.streamEncryptPrecomputedContract A stack) :=
  h.post_mono (streamEncryptPost_imp _)

/-- `Spec.Gcm.streamEncryptPrepared16Contract` from `streamEncryptPrepared16RoundsContract`. -/
theorem streamEncryptPrepared16_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptPrepared16RoundsContract A stack)) : Verified T c (Spec.Gcm.streamEncryptPrepared16Contract A stack) :=
  h.post_mono (streamEncryptPost_imp _)

/-- `Spec.Gcm.streamEncryptPreparedContract` from `streamEncryptPreparedRoundsContract`. -/
theorem streamEncryptPrepared_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptPreparedRoundsContract A stack)) : Verified T c (Spec.Gcm.streamEncryptPreparedContract A stack) :=
  h.post_mono (streamEncryptPost_imp _)

/-- `Spec.Gcm.streamFinishContract` from `streamFinishRoundsContract`. -/
theorem streamFinish_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamFinishRoundsContract A stack)) : Verified T c (Spec.Gcm.streamFinishContract A stack) :=
  h.post_mono (streamFinishPost_imp _)

/-- `Spec.Gcm.streamVerifyContract` from `streamVerifyRoundsContract`. -/
theorem streamVerify_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamVerifyRoundsContract A stack)) : Verified T c (Spec.Gcm.streamVerifyContract A stack) :=
  h.post_mono (streamVerifyPost_imp _)

end VG.Proof.AesGcm
