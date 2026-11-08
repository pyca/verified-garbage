module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM's prepared key context with a flag

The contracts that are to replace those of `Spec/Gcm/Prepared.lean`, whose
code is proven against them first (and registered once they do): a
prepared key context of 1088 bytes, whose word at byte 1024 is 1 when it
holds no powers (`PreparedRepr`), which a `prepare` that computes none
writes alone (one that computes them need not write it); the functions
reading it may branch on whether that word is 1, which they leak
(`flagLeak`), and take the code that reads only its first 256 bytes, the
key context of `vg_aes_gcm_init`, if it is. Pre- and postconditions are
those of the prepared contracts but for `PreparedRepr`; each has its
`*RoundsContract`, of `Proof/AesGcm/Rounds.lean`'s form, which the proofs
target, and its form with the key (`*_keyed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.Flag

open VG.Spec.Gcm

/-- The prepared key context at `p` either says it holds no powers (its word
at byte 1024 is 1) or holds them (`PreparedPowersRepr`). -/
def PreparedRepr (m : Mem) (p : Addr) : Prop :=
  m.readW (p + 1024) 64 = 1 ∨ PreparedPowersRepr m p

/-- What a function reading the prepared key context at `p` may leak of it:
whether it holds no powers. -/
def flagLeak (m : Mem) (p : Addr) : Nat := if m.readW (p + 1024) 64 = 1 then 1 else 0

/-! ## The key setup -/

/-- `vg_aes_gcm_prepare(ctx: *mut [u64; 136])`. -/
def prepareSig : Sig where
  params := [("ctx", .array true .u64 136)]

/-- Keeps the first 256 bytes, and makes the context a prepared one of its
hash subkey (`PreparedRepr`). -/
def preparePost (pb : Nat) : prepareSig.Post pb := fun ctx m m' _ =>
  Spec.Aes.bytesAt m' ctx 256 = Spec.Aes.bytesAt m ctx 256 ∧ PreparedRepr m' ctx

def prepareContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  prepareSig.contract A (post := preparePost A.ptrBits) (writeArgs := true) (stack := stack)

/-! ## The functions on it -/

def sealSig : Sig where
  params := [("ctx", .array false .u64 136), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16)]

def openSig : Sig where
  params := [("ctx", .array false .u64 136), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

def streamCryptSig : Sig where
  params := [("ctx", .array false .u64 136), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len")]

def sealGatherSig : Sig where
  params := [("ctx", .array false .u64 136), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

def openToSig : Sig where
  params := [("ctx", .array false .u64 136), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

def sealPre (pb : Nat) : Curry (sealSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PreparedRepr m ctx

def openPre (pb : Nat) : Curry (openSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PreparedRepr m ctx

def streamCryptPre (pb : Nat) : Curry (streamCryptSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PreparedRepr m ctx

def sealGatherPre (pb : Nat) : Curry (sealGatherSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedRepr m ctx

def openToPre (pb : Nat) : Curry (openToSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ PreparedRepr m ctx

def sealLeak (pb : Nat) : Curry (sealSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _nonce _nonceLen _aad _aadLen _data _len _tag m => [flagLeak m ctx]

def openLeak (pb : Nat) : Curry (openSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m =>
    flagLeak m ctx :: Spec.Gcm.openLeak pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m

def streamCryptLeak (pb : Nat) : Curry (streamCryptSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _state _aadLen _textLen _data _len m => [flagLeak m ctx]

def sealGatherLeak (pb : Nat) : Curry (sealGatherSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _nonce _nonceLen _aad _aadLen _src _srcCount _dst _len _tag m => [flagLeak m ctx]

def openToLeak (pb : Nat) : Curry (openToSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m =>
    flagLeak m ctx ::
      Spec.Gcm.openToLeak pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m

/-! ## Their contracts -/

def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealLeak A.ptrBits))

def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

def streamEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A (pre := streamCryptPre A.ptrBits) (post := streamEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptLeak A.ptrBits))

def streamDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A (pre := streamCryptPre A.ptrBits) (post := streamDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptLeak A.ptrBits))

def sealGatherContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherSig.contract A (pre := sealGatherPre A.ptrBits) (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealGatherLeak A.ptrBits))

def openToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToSig.contract A (pre := openToPre A.ptrBits) (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-! ## Their contracts with the number of rounds -/

def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := AesGcm.sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealLeak A.ptrBits))

def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := AesGcm.openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

def streamEncryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A (pre := streamCryptPre A.ptrBits)
    (post := AesGcm.streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptLeak A.ptrBits))

def streamDecryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A (pre := streamCryptPre A.ptrBits)
    (post := AesGcm.streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptLeak A.ptrBits))

def sealGatherRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherSig.contract A (pre := sealGatherPre A.ptrBits)
    (post := AesGcm.sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealGatherLeak A.ptrBits))

def openToRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToSig.contract A (pre := openToPre A.ptrBits) (post := AesGcm.openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-! ## With the key -/

theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (sealContract A stack) :=
  h.post_mono (AesGcm.sealPost_imp _)

theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (openContract A stack) :=
  h.post_mono (AesGcm.openPost_imp _)

theorem streamEncrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptRoundsContract A stack)) :
    Verified T c (streamEncryptContract A stack) :=
  h.post_mono (AesGcm.streamEncryptPost_imp _)

theorem streamDecrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptRoundsContract A stack)) :
    Verified T c (streamDecryptContract A stack) :=
  h.post_mono (AesGcm.streamDecryptPost_imp _)

theorem sealGather_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherRoundsContract A stack)) :
    Verified T c (sealGatherContract A stack) :=
  h.post_mono (AesGcm.sealGatherPost_imp _)

theorem openTo_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToRoundsContract A stack)) : Verified T c (openToContract A stack) :=
  h.post_mono (AesGcm.openToPost_imp _)

end VG.Proof.AesGcm.Flag
