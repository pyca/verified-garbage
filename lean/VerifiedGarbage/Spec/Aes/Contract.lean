module

public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.Artifact

/-!
# AES: the contracts of the key expansion and the block cipher, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_expand_key`, `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
in terms of `Spec/Aes.lean`, for any target: `A` is the target's calling
convention. The signatures fix where the arguments are, the memory each
function may access, disjointness, and that the pointers, the key's length,
the number of rounds and the number of blocks are public (see
`TCB/Sig.lean`).

The key schedule is stored as plain bytes (the words `w[0] … w[4Nr + 3]` in
order, each as its 4 bytes), which is also the layout AES-NI's round keys
use, so that every implementation of AES on a target reads the same
schedule.

`vg_aes_expand_key` keeps its working space on the stack (`stack` is the
number of bytes of stack below the stack pointer its frame uses, see
`Sig.contract`). `vg_aes_expand_key_scratch` is the same function with its
working space passed in `scratch`, for functions that call it with theirs.
-/

@[expose] public section

namespace VG.Spec.Aes

/-- `vg_aes_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 240])`.
The first `16 (Nr + 1)` bytes of `schedule` hold the key schedule on exit;
the rest of it is working space. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 240)]

/-- The key is of 16, 24 or 32 bytes. -/
def expandKeyPre (pb : Nat) : Curry (expandKeySig.words pb) (Mem → Prop) :=
  fun _key keyLen _schedule _ => keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32

/-- For a key of 16, 24 or 32 bytes at `key`: its key schedule (`expandKey`,
`16 (Nr + 1)` bytes for `Nr = key_len / 4 + 6` rounds) is at `schedule`.
Stated for those lengths, which the precondition requires, so that it reads
only the buffers. -/
def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key keyLen schedule m m' _ =>
  (keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32) →
    bytesAt m' schedule (16 * (rounds (keyLen.toNat / 4) + 1)) =
      expandKey (bytesAt m key keyLen.toNat)

/-- `expandKeyPre` and `expandKeyPost`: writes the key schedule of the key
at `key` to `schedule`. The key is secret. -/
def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A (pre := expandKeyPre A.ptrBits) (post := expandKeyPost A.ptrBits)
    (stack := stack)

/-- `vg_aes_expand_key` on every target. -/
def expandKeyApi : Api where
  module := "aes"
  name := "vg_aes_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "The AES key expansion (FIPS 197 §5.2, `KEYEXPANSION`): writes the key schedule of \
    the `key_len`-byte key at `key`, the words `w[0] … w[4 * Nr + 3]` for `Nr = key_len / 4 + 6` \
    rounds, each as its 4 bytes (`16 * (Nr + 1)` bytes in all), to the start of `*schedule`, as \
    `vg_aes_ctr32` reads it.\n\n\
    Contract: `VG.Spec.Aes.expandKeyContract`. Constant time: only the pointers and `key_len` may \
    affect timing, not the key."
  safety := [
    "`key_len` must be 16, 24 or 32.",
    "The bytes of `schedule` after the key schedule are unspecified on return."]

/-- `vg_aes_expand_key_scratch(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`:
`vg_aes_expand_key` with its working space passed in `scratch`, for
functions that call it with theirs (AES-GCM's, AES-GCM-SIV's, AES-SIV's,
AES-OCB's and CMAC's). The first `16 (Nr + 1)` bytes of `schedule` hold the
key schedule on exit; the rest of it, and `scratch`, are working space. -/
def expandKeyScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 240),
    ("scratch", .array true .u64 64)]

/-- For a key of 16, 24 or 32 bytes at `key`, writes its key schedule
(`expandKey`, `16 (Nr + 1)` bytes for `Nr = key_len / 4 + 6` rounds) to
`schedule`. The key is secret. -/
def expandKeyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeyScratchSig.contract A
    (pre := fun _key keyLen _schedule _scratch _ =>
      keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32)
    (post := fun key keyLen schedule _scratch m m' _ =>
      bytesAt m' schedule (16 * (rounds (keyLen.toNat / 4) + 1)) =
        expandKey (bytesAt m key keyLen.toNat))
    (stack := stack)

/-- `vg_aes_expand_key_scratch` on every target. -/
def expandKeyScratchApi : Api where
  module := "aes"
  name := "vg_aes_expand_key_scratch"
  sig := expandKeyScratchSig
  contracts := some fun A stack => expandKeyScratchContract A stack
  summary := "`vg_aes_expand_key`, with its working space in `*scratch`.\n\n\
    Contract: `VG.Spec.Aes.expandKeyScratchContract`. Constant time: only the pointers and \
    `key_len` may affect timing, not the key."
  safety := [
    "`key_len` must be 16, 24 or 32.",
    "The bytes of `schedule` after the key schedule are unspecified on return.",
    "The contents of `scratch` on return are unspecified."]

/-! ## The cipher and the inverse cipher on whole blocks -/

/-- The 16 bytes at `p` as a state: byte `i` is `in[i]` (§3.4). -/
def stateAt (m : Mem) (p : Addr) : State := Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.1)

/-- The `n` blocks of 16 bytes at `p`, as states. -/
def statesAt (m : Mem) (p : Addr) (n : Nat) : List State :=
  (List.range n).map fun i => stateAt m (p + BitVec.ofNat 64 (16 * i))

/-- `vg_aes_encrypt_blocks(schedule: *const [u8; 240], rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`,
and `vg_aes_decrypt_blocks` with the same signature. `rounds` is public;
`scratch` is working space. -/
def blocksSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("data", .slice true (.array .u8 16) "n"), ("scratch", .array true .u64 256)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces each of the `n` blocks at
`data` with `CIPHER(·, rounds, w)`. The key schedule and the data are
secret. -/
def encryptBlocksContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (pre := fun _schedule rounds _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds data n _scratch m m' _ =>
      statesAt m' data n.toNat =
        (statesAt m data n.toNat).map
          (cipher rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1)))))
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces each of the `n` blocks at
`data` with `INVCIPHER(·, rounds, w)`. The key schedule and the data are
secret. -/
def decryptBlocksContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (pre := fun _schedule rounds _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds data n _scratch m m' _ =>
      statesAt m' data n.toNat =
        (statesAt m data n.toNat).map
          (invCipher rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1)))))
    (stack := stack)

/-- `vg_aes_encrypt_blocks` on every target. -/
def encryptBlocksApi : Api where
  module := "aes"
  name := "vg_aes_encrypt_blocks"
  sig := blocksSig
  contracts := some fun A stack => encryptBlocksContract A stack
  summary := "AES encryption of whole blocks (FIPS 197 §5.1, `CIPHER`): replaces each of the `n` \
    16-byte blocks at `data` with its encryption by AES with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it.\n\n\
    Contract: `VG.Spec.Aes.encryptBlocksContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_aes_decrypt_blocks` on every target. -/
def decryptBlocksApi : Api where
  module := "aes"
  name := "vg_aes_decrypt_blocks"
  sig := blocksSig
  contracts := some fun A stack => decryptBlocksContract A stack
  summary := "AES decryption of whole blocks (FIPS 197 §5.3, `INVCIPHER`): replaces each of the \
    `n` 16-byte blocks at `data` with its decryption by AES with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it (the forward cipher's schedule, which the inverse cipher uses in the reverse \
    order).\n\n\
    Contract: `VG.Spec.Aes.decryptBlocksContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Aes
