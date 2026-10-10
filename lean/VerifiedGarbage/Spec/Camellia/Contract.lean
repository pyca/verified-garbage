module

public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.TCB.Artifact

/-!
# Camellia ECB: contracts on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_camellia_expand_key`, `vg_camellia_ecb_encrypt` and
`vg_camellia_ecb_decrypt`, in terms of `Spec/Camellia.lean`, for any target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers, the key's length, the number of rounds and the number of
blocks are public (see `TCB/Sig.lean`). Key bytes, subkeys and data are
secret.

The schedule is 272 bytes: the subkeys in the order encryption uses them
(`scheduleWords`), each as 8 bytes, the most significant first; a key of
16 bytes uses the first 208 (26 subkeys, 18 rounds), one of 24 or 32 all
272 (34 subkeys, 24 rounds). The functions keep their working space on the
stack (`stack`, see `Sig.contract`).

The Rust API rejects keys of other lengths before key expansion, and input
that is not whole blocks. It adds and removes no padding. Empty ECB input
is supported.
-/

@[expose] public section

namespace VG.Spec.Camellia

/-- `vg_camellia_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 272])`. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 272)]

/-- The key is of 16, 24 or 32 bytes. -/
def expandKeyPre (pb : Nat) : Curry (expandKeySig.words pb) (Mem → Prop) :=
  fun _key keyLen _schedule _ => keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32

/-- For a key of 16, 24 or 32 bytes at `key`: its subkeys (`expandKey`), as
stored (`scheduleBytes`: 208 bytes for a key of 16 bytes, 272 otherwise),
are at `schedule`. Stated for those lengths, which the precondition
requires, so that it reads only the buffers. -/
def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key keyLen schedule m m' _ =>
  (keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32) →
    bytesAt m' schedule (8 * scheduleLength (rounds keyLen.toNat)) =
      scheduleBytes (expandKey (bytesAt m key keyLen.toNat))

/-- `expandKeyPre` and `expandKeyPost`: writes the subkeys of the key at
`key` to `schedule`. The key is secret. -/
def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A (pre := expandKeyPre A.ptrBits) (post := expandKeyPost A.ptrBits)
    (stack := stack)

/-- `vg_camellia_expand_key` on every target. -/
def expandKeyApi : Api where
  module := "camellia"
  name := "vg_camellia_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "The Camellia key schedule (RFC 3713 §2.2): writes the subkeys of the `key_len`-byte \
    key at `key` to the start of `*schedule`, in the order encryption uses them (`kw1`, `kw2`, \
    then for each six rounds their subkeys `k` and, but after the last six, the two of `FL` and \
    `FLINV`, then `kw3`, `kw4`), each as 8 bytes, the most significant first: 26 subkeys \
    (208 bytes, for 18 rounds) for a key of 16 bytes, 34 (272 bytes, for 24 rounds) for one of \
    24 or 32, as `vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` read them.\n\n\
    Contract: `VG.Spec.Camellia.expandKeyContract`. Constant time: only the pointers and \
    `key_len` may affect timing, not the key."
  safety := [
    "`key_len` must be 16, 24 or 32.",
    "For a key of 16 bytes, the last 64 bytes of `schedule` are unspecified on return."]

/-- `vg_camellia_ecb_encrypt(schedule: *const [u8; 272], rounds: usize, data: *mut [u8; 16], n: usize)`,
and `vg_camellia_ecb_decrypt` with the same signature. `rounds` is public. -/
def ecbSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("data", .slice true (.array .u8 16) "n")]

/-- `rounds` is 18 or 24. -/
def ecbPre (pb : Nat) : Curry (ecbSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _data _n _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule` (`subkeysAt`): replaces each of the `n` blocks at `data` with its
encryption (or decryption) under them. Stated for those numbers of rounds,
which the precondition requires, so that it reads only the buffers. -/
def ecbPost (direction : Direction) (pb : Nat) : ecbSig.Post pb := fun schedule rounds data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    blocksAt m' data n.toNat =
      ecb (subkeysAt m schedule rounds.toNat) direction (blocksAt m data n.toNat)

/-- `ecbPre` and `ecbPost`. The subkeys and the data are secret. -/
def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (pre := ecbPre A.ptrBits) (post := ecbPost direction A.ptrBits) (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

/-- `vg_camellia_ecb_encrypt` on every target. -/
def ecbEncryptApi : Api where
  module := "camellia"
  name := "vg_camellia_ecb_encrypt"
  sig := ecbSig
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "Camellia ECB encryption (RFC 3713 §2.3, SP 800-38A §6.1): replaces each of the `n` \
    16-byte blocks at `data` with its encryption by Camellia with `rounds` rounds under the \
    subkeys at `schedule`, as `vg_camellia_expand_key` writes them. No padding is added or \
    removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Camellia.ecbEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

/-- `vg_camellia_ecb_decrypt` on every target. -/
def ecbDecryptApi : Api where
  module := "camellia"
  name := "vg_camellia_ecb_decrypt"
  sig := ecbSig
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "Camellia ECB decryption (RFC 3713 §2.3.3, SP 800-38A §6.1): replaces each of the \
    `n` 16-byte blocks at `data` with its decryption by Camellia with `rounds` rounds under the \
    subkeys at `schedule`, as `vg_camellia_expand_key` writes them (in the order encryption \
    uses them, which decryption reverses). No padding is added or removed. For `n = 0`, no \
    data is transformed.\n\n\
    Contract: `VG.Spec.Camellia.ecbDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
