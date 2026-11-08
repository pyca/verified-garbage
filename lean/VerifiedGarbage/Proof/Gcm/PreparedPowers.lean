module

public import VerifiedGarbage.Spec.Gcm.Prepared16

/-!
# AES-GCM with all 48 prepared powers: the contracts the proofs target

Not trusted: the contracts of the `*_prepared` functions on a 1024-byte key
context that holds the 48 prepared powers (`PreparedPowersRepr`), which the
implementations that read them are proven against; `Proof/AesGcm/Flag.lean`
lifts them to the contracts of `Spec/Gcm/Prepared.lean`, on a prepared key
context whose powers may be absent.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

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
