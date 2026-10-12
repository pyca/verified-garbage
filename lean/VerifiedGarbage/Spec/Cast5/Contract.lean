module

public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.TCB.Artifact

/-!
# CAST5 ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers and lengths. The key bytes, the subkeys and the data
are secret; the key's length and the number of rounds are public. The
schedule is `K1 … K32` (`Spec/Cast5.lean`), each a little-endian 32-bit
word (128 bytes). Each function takes a `scratch` buffer of working space,
whose contents on return are unspecified (the caller wipes it); `stack` is
the number of bytes of stack below the stack pointer that an
implementation's calls and frames use.

The Rust wrapper rejects invalid key lengths before key expansion, chooses
the number of rounds from the key's length (`rounds`), and rejects input
that is not a whole number of blocks. It does not add or remove padding.
Empty ECB input is supported.
-/

@[expose] public section

namespace VG.Spec.Cast5

/-- `vg_cast5_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 128],
scratch: *mut [u64; 32])`. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 128),
    ("scratch", .array true .u64 32)]

def expandKeyPre (pb : Nat) : Curry (expandKeySig.words pb) (Mem → Prop) :=
  fun _key keyLen _schedule _scratch _ => validKey keyLen.toNat

def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key keyLen schedule _scratch m m' _ =>
  scheduleAt m' schedule = expandKey (bytesAt m key keyLen.toNat)

/-- For `key_len` in 5–16: writes the subkeys of the `key_len` bytes at
`key` to `schedule`. -/
def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A (pre := expandKeyPre A.ptrBits) (post := expandKeyPost A.ptrBits)
    (stack := stack)

def expandKeyApi : Api where
  module := "cast5"
  name := "vg_cast5_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "CAST-128 (CAST5) key expansion (RFC 2144 §2.4): pads the `key_len` bytes at \
    `key` with zero bytes to 16 bytes (§2.5) and writes the subkeys `K1 … K32` to \
    `*schedule`, each a little-endian 32-bit word: the masking subkeys `Km1 … Km16`, then the \
    rotate subkeys `Kr1 … Kr16` (§2.4.1). A key of up to 10 bytes is used with 12 rounds, \
    a longer one with 16.\n\n\
    Contract: `VG.Spec.Cast5.expandKeyContract`. Constant time: only pointers and `key_len` \
    may affect timing, not the key bytes."
  safety := ["`key_len` must be in 5..=16.", "The contents of `scratch` on return are unspecified."]

/-- The ECB functions: `(schedule: *const [u8; 128], rounds: usize,
data: *mut [u8; 8], n: usize, scratch: *mut [u64; 32])`. `rounds` is public. -/
def ecbSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("data", .slice true (.array .u8 8) "n"), ("scratch", .array true .u64 32)]

def ecbPre (pb : Nat) : Curry (ecbSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _data _n _scratch _ => rounds.toNat = 12 ∨ rounds.toNat = 16

def ecbPost (direction : Direction) (pb : Nat) : ecbSig.Post pb :=
  fun schedule rounds data n _scratch m m' _ =>
    blocksAt m' data n.toNat =
      ecb (scheduleAt m schedule) rounds.toNat direction (blocksAt m data n.toNat)

/-- For `rounds` of 12 or 16: replaces the `n` blocks at `data` with their
encryption or decryption under the subkeys at `schedule`. -/
def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (pre := ecbPre A.ptrBits) (post := ecbPost direction A.ptrBits)
    (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

/-- The `# Safety` items the ECB functions share. -/
def ecbSafety : List String :=
  ["`rounds` must be 12 or 16.", "The contents of `scratch` on return are unspecified."]

def ecbEncryptApi : Api where
  module := "cast5"
  name := "vg_cast5_ecb_encrypt"
  sig := ecbSig
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "CAST-128 (CAST5) ECB encryption (RFC 2144 §2, SP 800-38A §6.1) of `n` complete \
    8-byte blocks at `data`, in place, with `rounds` rounds under the subkeys written by \
    `vg_cast5_expand_key`: 12 for a key of up to 10 bytes, 16 for a longer one (§2.5). \
    Only the least significant 5 bits of each rotate subkey are used. No padding is added. \
    For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Cast5.ecbEncryptContract`. Constant time: only pointers, `rounds` and \
    `n` may affect timing, not the subkeys or data, including S-box indices and rotation \
    amounts."
  safety := ecbSafety

def ecbDecryptApi : Api where
  module := "cast5"
  name := "vg_cast5_ecb_decrypt"
  sig := ecbSig
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "CAST-128 (CAST5) ECB decryption (RFC 2144 §2, SP 800-38A §6.1) of `n` complete \
    8-byte blocks at `data`, in place, with `rounds` rounds under the subkeys written by \
    `vg_cast5_expand_key`: 12 for a key of up to 10 bytes, 16 for a longer one (§2.5). \
    Only the least significant 5 bits of each rotate subkey are used. No padding is removed. \
    For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Cast5.ecbDecryptContract`. Constant time: only pointers, `rounds` and \
    `n` may affect timing, not the subkeys or data, including S-box indices and rotation \
    amounts."
  safety := ecbSafety

/-! ## Either direction

An implementation may share one body between the two directions: the ECB
functions above then call `vg_cast5_ecb`, which takes the direction as a
public argument. It is not part of the library's Rust API. -/

/-- `vg_cast5_ecb(schedule: *const [u8; 128], rounds: usize, data: *mut [u8; 8],
n: usize, scratch: *mut [u64; 32], decrypt: usize)`: the ECB functions' arguments,
then the direction (0 to encrypt, 1 to decrypt), which is public. -/
def ecbDirSig : Sig where
  params := ecbSig.params ++ [("decrypt", .int .usize true)]

/-- The direction `decrypt` selects. -/
def directionOf (decrypt : Nat) : Direction := if decrypt = 0 then .encrypt else .decrypt

def ecbDirPre (pb : Nat) : Curry (ecbDirSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _data _n _scratch decrypt _ =>
    (rounds.toNat = 12 ∨ rounds.toNat = 16) ∧ decrypt.toNat ≤ 1

def ecbDirPost (pb : Nat) : ecbDirSig.Post pb :=
  fun schedule rounds data n _scratch decrypt m m' _ =>
    blocksAt m' data n.toNat =
      ecb (scheduleAt m schedule) rounds.toNat (directionOf decrypt.toNat) (blocksAt m data n.toNat)

/-- For `rounds` of 12 or 16 and `decrypt` of 0 or 1: replaces the `n` blocks
at `data` with their encryption (`decrypt = 0`) or decryption (`decrypt = 1`)
under the subkeys at `schedule`. -/
def ecbDirContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbDirSig.contract A (pre := ecbDirPre A.ptrBits) (post := ecbDirPost A.ptrBits) (stack := stack)

def ecbDirApi : Api where
  module := "cast5"
  name := "vg_cast5_ecb"
  sig := ecbDirSig
  contracts := some fun A stack => ecbDirContract A stack
  summary := "CAST-128 (CAST5) ECB encryption (`decrypt = 0`) or decryption (`decrypt = 1`) \
    (RFC 2144 §2, SP 800-38A §6.1) of `n` complete 8-byte blocks at `data`, in place, with \
    `rounds` rounds under the subkeys written by `vg_cast5_expand_key`: what \
    `vg_cast5_ecb_encrypt` and `vg_cast5_ecb_decrypt` do, for implementations that share one \
    body between them. Only the least significant 5 bits of each rotate subkey are used. For \
    `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Cast5.ecbDirContract`. Constant time: only pointers, `rounds`, `n` and \
    `decrypt` may affect timing, not the subkeys or data, including S-box indices and rotation \
    amounts."
  safety := ecbSafety ++ ["`decrypt` must be 0 or 1."]

end VG.Spec.Cast5
