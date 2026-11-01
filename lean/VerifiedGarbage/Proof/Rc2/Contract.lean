module

public import VerifiedGarbage.Spec.Rc2.Contract

/-!
# RC2-CBC: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Rc2

open VG.Spec.Rc2

/-- `vg_rc2_expand_key(key: *const u8, key_len: usize, effective_bits: usize,
schedule: *mut [u8; 128], scratch: *mut [u64; 64])`. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("effective_bits", .int .usize true),
    ("schedule", .array true .u8 128), ("scratch", .array true .u64 64)]

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A
    (pre := fun _key keyLen effectiveBits _schedule _scratch _ =>
      validKey keyLen.toNat effectiveBits.toNat)
    (post := fun key keyLen effectiveBits schedule _scratch m m' _ =>
      scheduleAt m' schedule = expandKey (bytesAt m key keyLen.toNat) effectiveBits.toNat)
    (stack := stack)

/-- The block functions:
`(schedule: *const [u8; 128], data: *mut [u8; 8], scratch: *mut [u64; 32])`. -/
def blockSig : Sig where
  params := [("schedule", .array false .u8 128), ("data", .array true .u8 8),
    ("scratch", .array true .u64 32)]

def encryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = encryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def decryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = decryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

/-- The CBC functions:
`(schedule: *const [u8; 128], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize,
scratch: *mut [u64; 64])`. Scratch includes room outside the block
primitive's working space to preserve the chaining value during decryption. -/
def cbcSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n"), ("scratch", .array true .u64 64)]

def cbcContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A
    (post := fun schedule iv data n _scratch m m' _ =>
      let result := cbc (scheduleAt m schedule) direction (blockAt m iv) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = result.1 ∧ blockAt m' iv = result.2)
    (writeArgs := true)
    (stack := stack)

def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcContract A .encrypt stack

def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcContract A .decrypt stack

end VG.Proof.Rc2
