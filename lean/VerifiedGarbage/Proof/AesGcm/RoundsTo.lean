module

-- separate module: target-independent, for every target's proof of `vg_aes_gcm_open_to`; in `Rounds.lean` it would rebuild every AES-GCM proof

public import VerifiedGarbage.Proof.AesGcm.Rounds

/-!
# AES-GCM decryption out of place: the contracts on the key context and the number of rounds

Not trusted: the contracts that the proofs of `vg_aes_gcm_open_to` and its
instances for prepared key contexts are written against, as
`Proof/AesGcm/Rounds.lean` states those of the other functions: for the
cipher and the hash subkey of the key context given (`Spec.Gcm.ctxCiph`,
`Spec.Gcm.ctxH`), from which the shared contracts of
`Spec/Gcm/OutOfPlace.lean`, `Spec/Gcm/Prepared.lean` and
`Spec/Gcm/Prepared16.lean` follow (`openTo_keyed`), and those of its
instance with the powers in a buffer of their own (`Spec/Gcm/Powers8.lean`,
`openToWithPowers_keyed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec
open VG.Spec.Gcm

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if `tag_len` is a tag length
`tagLenOk` allows and the tag is that of the `len` bytes of ciphertext at
`src` and the `aad_len` bytes of additional data at `aad`, with the IV the
`nonce_len` bytes at `nonce` (GCM-AD, `decryptWith`), the result is 1 and
the plaintext is the `len` bytes at `dst`; otherwise the result is 0 and the
`len` bytes at `dst` are zero. -/
def openToRoundsPost (pb : Nat) : openToSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst _dstLen tag tagLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m src len.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' dst len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' dst len.toNat = List.replicate len.toNat 0

/-- `openToRoundsPost`, for an output as long as the input (`openToPre`);
it may leak what `Spec.Gcm.openToContract` may (`openToLeak`). -/
def openToRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToSig.contract A (pre := openToPre A.ptrBits) (post := openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-- The unchanged `openToRoundsContract` postcondition with prepared powers. -/
def openToPreparedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedSig.contract A (pre := openToPreparedPre A.ptrBits)
    (post := openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-- The unchanged `openToRoundsContract` postcondition with 16 prepared powers. -/
def openToPrepared16RoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedSig.contract A (pre := openToPrepared16Pre A.ptrBits)
    (post := openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-- `openToRoundsPost`, which does not depend on `pw`. -/
def openToWithPowersRoundsPost (pb : Nat) : openToWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _pw m m' r =>
    openToRoundsPost pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m m' r

/-- `openToWithPowersPre`, `openToWithPowersRoundsPost`, and what
`Spec.Gcm.openToWithPowersContract` may leak (`openToWithPowersLeak`). -/
def openToWithPowersRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToWithPowersSig.contract A (pre := openToWithPowersPre A.ptrBits)
    (post := openToWithPowersRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openToWithPowersLeak A.ptrBits))

theorem openToPost_imp (pb : Nat) : openToSig.PostImp pb (openToRoundsPost pb) (Spec.Gcm.openToPost pb) :=
  fun ctx rounds _ _ _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [openToRoundsPost, Spec.Gcm.openToPost] at hp ⊢
    obtain ⟨hc, hh, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hh] at h'
    split
    all_goals
      rename_i heq
      rw [heq] at h'
      exact h'

/-- `Spec.Gcm.openToContract` from `openToRoundsContract`. -/
theorem openTo_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToRoundsContract A stack)) : Verified T c (Spec.Gcm.openToContract A stack) :=
  h.post_mono (openToPost_imp _)

/-- `Spec.Gcm.openToPreparedContract` from `openToPreparedRoundsContract`. -/
theorem openToPrepared_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToPreparedRoundsContract A stack)) : Verified T c (Spec.Gcm.openToPreparedContract A stack) :=
  h.post_mono (openToPost_imp _)

/-- `Spec.Gcm.openToPrepared16Contract` from `openToPrepared16RoundsContract`. -/
theorem openToPrepared16_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToPrepared16RoundsContract A stack)) :
    Verified T c (Spec.Gcm.openToPrepared16Contract A stack) :=
  h.post_mono (openToPost_imp _)

theorem openToWithPowersPost_imp (pb : Nat) :
    openToWithPowersSig.PostImp pb (openToWithPowersRoundsPost pb) (Spec.Gcm.openToWithPowersPost pb) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _ m m' r hp =>
    openToPost_imp pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m m' r hp

/-- `Spec.Gcm.openToWithPowersContract` from `openToWithPowersRoundsContract`. -/
theorem openToWithPowers_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToWithPowersRoundsContract A stack)) :
    Verified T c (Spec.Gcm.openToWithPowersContract A stack) :=
  h.post_mono (openToWithPowersPost_imp _)

end VG.Proof.AesGcm
