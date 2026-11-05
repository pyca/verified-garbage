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

/-! ## CBC on blocks

The internal CBC functions' contracts are stated with `cbcBlocks`, on blocks as
vectors, returning the chaining value to continue from;
`Proof/Rc2/Stream.lean` proves it is CBC (`Spec.Cbc.encrypt`,
`Spec.Cbc.decrypt`), as `Spec.Rc2.update` states it. -/

def xorBlock (a b : Block) : Block :=
  Vector.ofFn fun i => a[i] ^^^ b[i]

/-- One block of CBC, returning `(output, next IV)`. Decryption retains the
original ciphertext as the next IV, including for an in-place caller. -/
def cbcStep (k : Schedule) (direction : Direction) (iv input : Block) : Block × Block :=
  match direction with
  | .encrypt => let out := encryptBlock k (xorBlock input iv); (out, out)
  | .decrypt => (xorBlock (decryptBlock k input) iv, input)

/-- CBC on complete blocks, including the final chaining value. On empty
input the output is empty and the IV is unchanged. -/
def cbcBlocks (k : Schedule) (direction : Direction) (iv : Block) :
    List Block → List Block × Block
  | [] => ([], iv)
  | b :: bs =>
    let (out, iv') := cbcStep k direction iv b
    let (rest, last) := cbcBlocks k direction iv' bs
    (out :: rest, last)

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
      let result := cbcBlocks (scheduleAt m schedule) direction (blockAt m iv) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = result.1 ∧ blockAt m' iv = result.2)
    (writeArgs := true)
    (stack := stack)

def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcContract A .encrypt stack

def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcContract A .decrypt stack

end VG.Proof.Rc2
