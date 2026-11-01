module

public import VerifiedGarbage.Spec.Seed.Contract

/-!
# SEED: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Seed

open VG.Spec.Seed

/-! ## Blocks, with the working space as an argument

`vg_seed_encrypt_blocks` and `vg_seed_decrypt_blocks` are ECB with the
working space supplied by the caller (`scratch`), as `vg_aes_encrypt_blocks`
is for AES: functions built on SEED (its modes) call them for each batch of
blocks without allocating and wiping a working space on every call. The
working space's size, 1088 bytes, is enough for every target's ECB code. -/

/-! ## Either direction

An implementation may share one body between the two directions: SEED's ECB
functions then call `vg_seed_ecb`, which takes the direction as a
public argument. It is not part of the library's Rust API. -/

def blocksSig : Sig where
  params := [("schedule", .array false .u8 128), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 136)]

/-- `ecbPost`, whatever `scratch` holds afterwards. -/
def blocksContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (post := fun schedule data n _scratch => ecbPost direction A.ptrBits schedule data n)
    (writeArgs := true) (stack := stack)

/-- The direction `decrypt` selects: 0 to encrypt, otherwise decrypt. -/
def directionOf (decrypt : Nat) : Direction := if decrypt = 0 then .encrypt else .decrypt

/-- `vg_seed_ecb(schedule, data, n, decrypt: usize)`: the ECB functions'
arguments, then the direction (0 to encrypt, 1 to decrypt), which is public. -/
def ecbDirSig : Sig where
  params := ecbSig.params ++ [("decrypt", .int .usize true)]

/-- For `decrypt` of 0 or 1: replaces the `n` blocks at `data` with their
encryption (`decrypt = 0`) or decryption (`decrypt = 1`) under the round keys
at `schedule`. -/
def ecbDirContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbDirSig.contract A
    (pre := fun _schedule _data _n decrypt _ => decrypt.toNat ≤ 1)
    (post := fun schedule data n decrypt m m' _ =>
      blocksAt m' data n.toNat =
        ecb (scheduleAt m schedule) (directionOf decrypt.toNat) (blocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

end VG.Proof.Seed
