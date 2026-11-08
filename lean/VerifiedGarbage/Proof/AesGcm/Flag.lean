module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM's functions on a prepared key context, with the number of rounds

The contracts of `Spec/Gcm/Prepared.lean`'s functions on a prepared key
context (`PreparedRepr`, whose powers may be absent) in the form of
`Proof/AesGcm/Rounds.lean`, which the proofs target (`*RoundsContract`), and
from them the contracts with the key (`*_keyed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.Flag

open VG.Spec.Gcm

/-! ## Their contracts with the number of rounds -/

def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPreparedPre A.ptrBits) (post := AesGcm.sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealPreparedLeak A.ptrBits))

def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPreparedPre A.ptrBits) (post := AesGcm.openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openPreparedLeak A.ptrBits))

def streamEncryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := AesGcm.streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptPreparedLeak A.ptrBits))

def streamDecryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := AesGcm.streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptPreparedLeak A.ptrBits))

def sealGatherRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPreparedPre A.ptrBits)
    (post := AesGcm.sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealGatherPreparedLeak A.ptrBits))

def openToRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedSig.contract A (pre := openToPreparedPre A.ptrBits) (post := AesGcm.openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToPreparedLeak A.ptrBits))

/-! ## With the key -/

theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (sealPreparedContract A stack) :=
  h.post_mono (AesGcm.sealPost_imp _)

theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (openPreparedContract A stack) :=
  h.post_mono (AesGcm.openPost_imp _)

theorem streamEncrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptRoundsContract A stack)) :
    Verified T c (streamEncryptPreparedContract A stack) :=
  h.post_mono (AesGcm.streamEncryptPost_imp _)

theorem streamDecrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptRoundsContract A stack)) :
    Verified T c (streamDecryptPreparedContract A stack) :=
  h.post_mono (AesGcm.streamDecryptPost_imp _)

theorem sealGather_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherRoundsContract A stack)) :
    Verified T c (sealGatherPreparedContract A stack) :=
  h.post_mono (AesGcm.sealGatherPost_imp _)

theorem openTo_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToRoundsContract A stack)) : Verified T c (openToPreparedContract A stack) :=
  h.post_mono (AesGcm.openToPost_imp _)

end VG.Proof.AesGcm.Flag
