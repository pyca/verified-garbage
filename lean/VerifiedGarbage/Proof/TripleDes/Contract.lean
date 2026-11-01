module

public import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

/-! ## ECB with its working space as an argument

The ECB functions keep their working space in a frame of their own. The
same computation with the working space passed in (`scratch`, 1024 bytes,
whatever it holds) is a function of its own, so that the ECB functions of a
target, each with its own wide loop for the blocks it handles at a time, can
call one copy of the code for the blocks left. -/

/-! ## Either direction

An implementation may share one body between the two directions: the
block or ECB functions then call `vg_triple_des_crypt_block` or
`vg_triple_des_ecb`, which take the direction as a public argument. They are
not part of the library's Rust API. -/

def blockSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .array true .u8 8),
    ("scratch", .array true .u64 64)]

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

def ecbCoreSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .slice true (.array .u8 8) "n"),
    ("scratch", .array true .u64 128)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbCoreContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbCoreSig.contract A
    (post := fun schedule data n _scratch => ecbPost direction A.ptrBits schedule data n)
    (writeArgs := true) (stack := stack)

def ecbEncryptCoreContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbCoreContract A .encrypt stack

def ecbDecryptCoreContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbCoreContract A .decrypt stack

/-- The direction `decrypt` selects: 0 to encrypt, otherwise decrypt. -/
def directionOf (decrypt : Nat) : Direction := if decrypt = 0 then .encrypt else .decrypt

/-- The block function of a direction. -/
def cryptBlock (k : Schedule) : Direction → Block → Block
  | .encrypt => encryptBlock k
  | .decrypt => decryptBlock k

/-- `vg_triple_des_ecb(schedule, data, n, decrypt: usize)`. -/
def ecbDirSig : Sig where
  params := ecbSig.params ++ [("decrypt", .int .usize true)]

def ecbDirContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbDirSig.contract A
    (pre := fun _schedule _data _n decrypt _ => decrypt.toNat ≤ 1)
    (post := fun schedule data n decrypt m m' _ =>
      blocksAt m' data n.toNat =
        ecb (scheduleAt m schedule) (directionOf decrypt.toNat) (blocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

end VG.Proof.TripleDes
