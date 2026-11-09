module

public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM with 48 or 16 prepared powers: the contracts the proofs target

Not trusted: the contracts of the `*_prepared` functions on a 1024-byte key
context that holds the 48 prepared powers (`PreparedPowersRepr`), or the first
16 (`PreparedPowers16Repr`), which the implementations that read them are
proven against; `Proof/AesGcm/Flag.lean` lifts them to the contracts of
`Spec/Gcm/Prepared.lean`, on a prepared key context whose count says which
powers are present.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-! ## The first 16 powers -/

/-- A 1024-byte context, whose first 256 bytes are a key context. -/
def prepare16Sig : Sig where
  params := [("ctx", .array true .u64 128)]

/-- Keeps the first 256 bytes, and writes the first 16 prepared powers of the
hash subkey in its bytes 240–255 (`ctxH`). With those bytes a key context
(`KeyRepr`, as `vg_aes_gcm_init` writes it), the result is a 16-power
prepared key context of the same key (`KeyRepr` and `PreparedPowers16Repr`). -/
def prepare16Post (pb : Nat) : prepare16Sig.Post pb := fun ctx m m' _ =>
  Aes.bytesAt m' ctx 256 = Aes.bytesAt m ctx 256 ∧ PreparedPowers16Repr m' ctx

/-- No precondition: the powers are those of whatever hash subkey the
context holds. -/
def prepare16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  prepare16Sig.contract A (post := prepare16Post A.ptrBits) (writeArgs := true) (stack := stack)

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def sealPrepared16Pre (pb : Nat) : Curry (sealPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def openPrepared16Pre (pb : Nat) : Curry (openPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def streamCryptPrepared16Pre (pb : Nat) : Curry (streamCryptPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def sealGatherPrepared16Pre (pb : Nat) : Curry (sealGatherPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def openToPrepared16Pre (pb : Nat) : Curry (openToPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ PreparedPowers16Repr m ctx

/-- The unchanged `sealContract` postcondition with 16 prepared powers. -/
def sealPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrecomputedSig.contract A (pre := sealPrepared16Pre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `openContract` postcondition with 16 prepared powers. -/
def openPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrecomputedSig.contract A (pre := openPrepared16Pre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- The unchanged `streamEncryptContract` postcondition with 16 prepared powers. -/
def streamEncryptPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamCryptPrepared16Pre A.ptrBits)
    (post := streamEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `streamDecryptContract` postcondition with 16 prepared powers. -/
def streamDecryptPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamCryptPrepared16Pre A.ptrBits)
    (post := streamDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `sealGatherContract` postcondition with 16 prepared powers. -/
def sealGatherPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrecomputedSig.contract A (pre := sealGatherPrepared16Pre A.ptrBits)
    (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `openToContract` postcondition with 16 prepared powers. -/
def openToPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPrecomputedSig.contract A (pre := openToPrepared16Pre A.ptrBits)
    (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-! ## All 48 powers -/

/-- Keeps the first 256 bytes, and writes the 48 prepared powers. -/
def preparePowersPost (pb : Nat) : prepare16Sig.Post pb := fun ctx m m' _ =>
  Aes.bytesAt m' ctx 256 = Aes.bytesAt m ctx 256 ∧ PreparedPowersRepr m' ctx

/-- `vg_aes_gcm_prepare` writing the powers, on a 1024-byte context. -/
def preparePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  prepare16Sig.contract A (post := preparePowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- The existing round-count and length requirements, plus the 48 prepared powers. -/
def sealPowersPre (pb : Nat) : Curry (sealPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing round-count and length requirements, plus the 48 prepared powers. -/
def openPowersPre (pb : Nat) : Curry (openPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing round-count and length requirements, plus the 48 prepared powers. -/
def streamCryptPowersPre (pb : Nat) : Curry (streamCryptPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing round-count and length requirements, plus the 48 prepared powers. -/
def sealGatherPowersPre (pb : Nat) : Curry (sealGatherPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedPowersRepr m ctx

/-- The existing round-count and length requirements, plus the 48 prepared powers. -/
def openToPowersPre (pb : Nat) : Curry (openToPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ PreparedPowersRepr m ctx

/-- The unchanged contract with the 48 prepared powers. -/
def sealPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrecomputedSig.contract A (pre := sealPowersPre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged contract with the 48 prepared powers. -/
def openPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrecomputedSig.contract A (pre := openPowersPre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- The unchanged contract with the 48 prepared powers. -/
def streamEncryptPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamCryptPowersPre A.ptrBits)
    (post := streamEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged contract with the 48 prepared powers. -/
def streamDecryptPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamCryptPowersPre A.ptrBits)
    (post := streamDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged contract with the 48 prepared powers. -/
def sealGatherPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrecomputedSig.contract A (pre := sealGatherPowersPre A.ptrBits)
    (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged contract with the 48 prepared powers. -/
def openToPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPrecomputedSig.contract A (pre := openToPowersPre A.ptrBits)
    (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

end VG.Proof.Gcm
