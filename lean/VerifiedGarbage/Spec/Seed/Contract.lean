module

public import VerifiedGarbage.Spec.Seed
public import VerifiedGarbage.TCB.Artifact

/-!
# SEED ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers/lengths. Key bytes, round keys and data are secret.
The schedule has 32 little-endian 32-bit round keys (128 bytes),
`K1,0`, `K1,1`, …, `K16,1`. `stack` accounts for frames and calls; ECB
permits writes to ABI argument areas to call block primitives.

The Rust wrapper will reject input that is not a whole number of 16-byte
blocks. It will not add or remove padding. Empty ECB input is supported.
-/

@[expose] public section

namespace VG.Spec.Seed

def expandKeySig : Sig where
  params := [("key", .array false .u8 16), ("schedule", .array true .u8 128)]

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A
    (post := fun key schedule m m' _ => scheduleAt m' schedule = expandKey (blockAt m key))
    (stack := stack)

def expandKeyApi : Api where
  module := "seed"
  name := "vg_seed_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "SEED key expansion (RFC 4269 §2.3): expands the 16-byte key at `key` into \
    the sixteen rounds' 64-bit round keys `Ki0 || Ki1`, written to `schedule` as 32 \
    little-endian 32-bit words `K1,0`, `K1,1`, …, `K16,0`, `K16,1`.\n\n\
    Contract: `VG.Spec.Seed.expandKeyContract`. Constant time: only pointers may affect \
    timing, not key bytes."
  safety := []

def ecbSig : Sig where
  params := [("schedule", .array false .u8 128), ("data", .slice true (.array .u8 16) "n")]

def ecbPost (direction : Direction) (pb : Nat) : ecbSig.Post pb := fun schedule data n m m' _ =>
  blocksAt m' data n.toNat = ecb (scheduleAt m schedule) direction (blocksAt m data n.toNat)

def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (post := ecbPost direction A.ptrBits) (writeArgs := true) (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbEncryptApi : Api where
  module := "seed"
  name := "vg_seed_ecb_encrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "SEED ECB encryption (RFC 4269 §2, SP 800-38A §6.1) of `n` complete 16-byte \
    blocks at `data`, in place, under the schedule written by `vg_seed_expand_key`. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Seed.ecbEncryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := []

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

def ecbDecryptApi : Api where
  module := "seed"
  name := "vg_seed_ecb_decrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "SEED ECB decryption (RFC 4269 §2.4, SP 800-38A §6.1) of `n` complete 16-byte \
    blocks at `data`, in place, under the schedule written by `vg_seed_expand_key`: the \
    encryption procedure with the round keys in reverse order. No padding is added or \
    removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Seed.ecbDecryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := []

/-! ## Blocks, with the working space as an argument

`vg_seed_encrypt_blocks` and `vg_seed_decrypt_blocks` are ECB with the
working space supplied by the caller (`scratch`), as `vg_aes_encrypt_blocks`
is for AES: functions built on SEED (its modes) call them for each batch of
blocks without allocating and wiping a working space on every call. The
working space's size, 1088 bytes, is enough for every target's ECB code. -/

def blocksSig : Sig where
  params := [("schedule", .array false .u8 128), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 136)]

/-- `ecbPost`, whatever `scratch` holds afterwards. -/
def blocksContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (post := fun schedule data n _scratch => ecbPost direction A.ptrBits schedule data n)
    (writeArgs := true) (stack := stack)

def encryptBlocksApi : Api where
  module := "seed"
  name := "vg_seed_encrypt_blocks"
  sig := blocksSig
  writeArgs := true
  contracts := some fun A stack => blocksContract A .encrypt stack
  summary := "SEED encryption of whole blocks (RFC 4269 §2, SP 800-38A §6.1): replaces each of \
    the `n` 16-byte blocks at `data` with its encryption under the schedule written by \
    `vg_seed_expand_key`, with the working space in `*scratch`. For `n = 0`, no data is \
    transformed.\n\n\
    Contract: `VG.Spec.Seed.blocksContract`. Constant time: only pointers and `n` may affect \
    timing, not the schedule or data, including S-box inputs."
  safety := ["The contents of `scratch` on return are unspecified."]

def decryptBlocksApi : Api where
  module := "seed"
  name := "vg_seed_decrypt_blocks"
  sig := blocksSig
  writeArgs := true
  contracts := some fun A stack => blocksContract A .decrypt stack
  summary := "SEED decryption of whole blocks (RFC 4269 §2.4, SP 800-38A §6.1): replaces each \
    of the `n` 16-byte blocks at `data` with its decryption under the schedule written by \
    `vg_seed_expand_key` (the encryption procedure with the round keys in reverse order), \
    with the working space in `*scratch`. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Seed.blocksContract`. Constant time: only pointers and `n` may affect \
    timing, not the schedule or data, including S-box inputs."
  safety := ["The contents of `scratch` on return are unspecified."]

/-! ## Either direction

An implementation may share one body between the two directions: the ECB
functions above then call `vg_seed_ecb`, which takes the direction as a
public argument. It is not part of the library's Rust API. -/

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

end VG.Spec.Seed
