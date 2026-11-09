module

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.Gcm.PreparedContract

/-!
# AES-GCM with 16 prepared powers: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def streamEncryptToPrepared16Pre (pb : Nat) :
    Curry (streamEncryptToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _src len _dst dstLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen = len ∧ PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def sealSplitPrepared16Pre (pb : Nat) : Curry (sealSplitPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src srcLen _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ srcLen.toNat ≤ len.toNat ∧
      PreparedPowers16Repr m ctx

/-- The unchanged `streamEncryptToContract` postcondition with 16 prepared powers. -/
def streamEncryptToPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPreparedSig.contract A (pre := streamEncryptToPrepared16Pre A.ptrBits)
    (post := streamEncryptToPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `sealSplitContract` postcondition with 16 prepared powers. -/
def sealSplitPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPreparedSig.contract A (pre := sealSplitPrepared16Pre A.ptrBits)
    (post := sealSplitPost A.ptrBits)
    (writeArgs := true) (stack := stack)

end VG.Proof.Gcm
