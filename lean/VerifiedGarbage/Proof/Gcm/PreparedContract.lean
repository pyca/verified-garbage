module

public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.Gcm.PrecomputedContract

/-!
# AES-GCM with prepared powers: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- The existing signature with a prepared 1024-byte context. -/
abbrev cryptBlocksPreparedSig := cryptBlocksPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def cryptBlocksPreparedPre (pb : Nat) : Curry (cryptBlocksPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _data _n _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev encryptBlocksToPreparedSig := encryptBlocksToPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def encryptBlocksToPreparedPre (pb : Nat) : Curry (encryptBlocksToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _src n _dst dstN _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstN = n ∧ PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev streamEncryptToPreparedSig := streamEncryptToPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def streamEncryptToPreparedPre (pb : Nat) : Curry (streamEncryptToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _src len _dst dstLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen = len ∧ PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev sealSplitPreparedSig := sealSplitPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def sealSplitPreparedPre (pb : Nat) : Curry (sealSplitPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src srcLen _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ srcLen.toNat ≤ len.toNat ∧
      PreparedPowersRepr m ctx

/-- The unchanged `encryptBlocksContract` postcondition with prepared powers. -/
def encryptBlocksPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPreparedSig.contract A (pre := cryptBlocksPreparedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- The unchanged `decryptBlocksContract` postcondition with prepared powers. -/
def decryptBlocksPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPreparedSig.contract A (pre := cryptBlocksPreparedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := blocksAt m data n.toNat
      blocksAt m' data n.toNat = ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- The unchanged `encryptBlocksToContract` postcondition with prepared powers. -/
def encryptBlocksToPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksToPreparedSig.contract A (pre := encryptBlocksToPreparedPre A.ptrBits)
    (post := encryptBlocksToPost A.ptrBits)
    (stack := stack)

/-- The unchanged `streamEncryptToContract` postcondition with prepared powers. -/
def streamEncryptToPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPreparedSig.contract A (pre := streamEncryptToPreparedPre A.ptrBits)
    (post := streamEncryptToPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The unchanged `sealSplitContract` postcondition with prepared powers. -/
def sealSplitPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPreparedSig.contract A (pre := sealSplitPreparedPre A.ptrBits)
    (post := sealSplitPost A.ptrBits)
    (writeArgs := true) (stack := stack)

end VG.Proof.Gcm
