module
public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.TCB.Artifact

/-!
# Camellia with its subkeys prepared once, in a working space

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

Two callable pieces of Camellia's modes. A bitsliced implementation turns
the subkeys into a table of its own (their bits as masks of its lanes)
before it transforms any block, at about the cost of a batch of blocks:
`vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` do so on every call.
The modes transform one batch at a time, so they prepare the table once, in
their working space, with `vg_camellia_prepare_keys`, and then transform
each batch with `vg_camellia_crypt_prepared`, which reads the table where
the preparation wrote it.

A `Layout`, which the implementation's proof chooses for its working space,
gives the table's ranges and its encoding (`encode`) for each number of
rounds: what `vg_camellia_prepare_keys` writes there for the subkeys of that
many rounds in the order of a direction, and what
`vg_camellia_crypt_prepared` needs to find there to transform its blocks in
that direction. It also gives the offset of the batch's `blocks` blocks, and
the ranges each function may change. The two functions are only ever
composed, so the encoding is the implementation's: whatever it is, the
batch's postcondition holds only where the table encodes the subkeys of a
direction, and then says that the batch is ECB in that direction
(`Spec/Camellia.lean`).

The table encodes the subkeys as the schedule's words (`wordsAt`), in the
order encryption uses them, which `subkeysOfWords` turns into the subkeys
of that many rounds: any list of words gives subkeys of that many rounds,
so a table that encodes some words says which subkeys a batch uses. (Not
every `Subkeys` is the subkeys of 18 or 24 rounds: its lists may have
any lengths, and encryption makes one round of each pair in `k`.)

Both functions take the number of rounds (18 or 24, public), as ECB does:
the batch's rounds and its control flow follow it, and the table, which is
secret, does not tell it.

Every byte of the working space outside a function's ranges keeps its
value, so the table survives the batches, which do not change it. The
subkeys, the table and the blocks are secret; the working space's address
and length, the number of rounds and the direction are public.

## For an implementation that only encrypts

`vg_camellia_prepare_encrypt_keys` prepares the subkeys in the order
encryption uses them, and `vg_camellia_encrypt_prepared` encrypts the
blocks of the working space under them. The feedback modes (OFB, CFB in
both directions and CBC encryption) use only Camellia's forward cipher, one
block at a time, so an implementation built for them (e.g. a serial core
that encrypts one block in registers) prepares no decryption order, which
`vg_camellia_prepare_keys` requires. These use only the direction
`.encrypt` of a `Layout`: the table encodes the schedule's words
(`encode rounds w .encrypt`), the batch's `blocks` blocks are at `buf`, and
each function changes only its ranges.
-/

@[expose] public section

namespace VG.Proof.Camellia.Prepared

open VG.Spec VG.Spec.Camellia

/-- The direction of `decrypt`: 0 to encrypt, anything else to decrypt. -/
def directionOf (decrypt : Nat) : Direction := if decrypt = 0 then .encrypt else .decrypt

/-- The schedule's `8 (rounds / 6) + 2` words at `p`, in the order encryption
uses them: the words of `subkeysAt m p rounds`. -/
def wordsAt (m : Mem) (p : Addr) (rounds : Nat) : List (BitVec 64) :=
  (List.range (scheduleLength rounds)).map fun i => wordAt m (p + BitVec.ofNat 64 (8 * i))

theorem subkeysAt_eq (m : Mem) (p : Addr) (rounds : Nat) :
    subkeysAt m p rounds = subkeysOfWords rounds (wordsAt m p rounds) := rfl

/-- Where an implementation keeps the prepared subkeys and the batch's
blocks in its working space, and how it encodes the subkeys, for each
number of rounds. -/
structure Layout where
  /-- The ranges `(offset, bytes)` of the working space that hold the
  prepared subkeys of that many rounds. -/
  table : Nat → List (Nat × Nat)
  /-- The byte at an offset of those ranges, for that many rounds and the
  schedule's words `w` (the subkeys `subkeysOfWords rounds w`) in the order
  of the direction. -/
  encode : Nat → List (BitVec 64) → Direction → Nat → Byte
  /-- The batch's blocks, at a byte offset. -/
  buf : Nat
  blocks : Nat
  /-- The ranges of the working space that the preparation may change, the
  table's among them. -/
  prepScratch : List (Nat × Nat)
  /-- The ranges that a batch may change, the blocks' among them and not
  the table's. -/
  cryptScratch : List (Nat × Nat)
  /-- The bytes of the working space that the functions use. -/
  size : Nat

/-- The table of the working space at `ws` encodes the schedule's words `w`
of `rounds` rounds in the order of the direction `d`. -/
def Holds (L : Layout) (m : Mem) (ws : Addr) (rounds : Nat) (w : List (BitVec 64)) (d : Direction) : Prop :=
  ∀ r ∈ L.table rounds, ∀ i < r.2, m (ws + BitVec.ofNat 64 (r.1 + i)) = L.encode rounds w d (r.1 + i)

/-- Every byte of `ws` outside the ranges `rs` keeps its value. -/
def Keeps (ws : Addr) (wsLen : Nat) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-! ## The preparation -/

/-- `vg_camellia_prepare_keys(schedule, rounds, decrypt, ws, ws_len)`: the
subkeys, the number of rounds and the direction (0 to encrypt, 1 to
decrypt), both public, and the working space, in 64-bit words. -/
def prepareSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true), ("decrypt", .int .usize true),
    ("ws", .slice true .u64 "ws_len")]

/-- For `rounds` of 18 or 24, `decrypt` of 0 or 1 and a working space of at
least `L.size` bytes: the table encodes the words of the subkeys of
`rounds` rounds at `schedule` in the order of the direction `decrypt` selects. Only the bytes
of `L.prepScratch` change. -/
def prepareContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  prepareSig.contract A
    (pre := fun _schedule rounds decrypt _ws wsLen _ =>
      (rounds.toNat = 18 ∨ rounds.toNat = 24) ∧ decrypt.toNat ≤ 1 ∧ L.size ≤ 8 * wsLen.toNat)
    (post := fun schedule rounds decrypt ws wsLen m m' _ =>
      Holds L m' ws rounds.toNat (wordsAt m schedule rounds.toNat) (directionOf decrypt.toNat) ∧
        Keeps ws wsLen.toNat L.prepScratch m m')
    (stack := stack)

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared(rounds, ws, ws_len)`: the number of rounds,
public, and the working space, in 64-bit words. -/
def cryptSig : Sig where
  params := [("rounds", .int .usize true), ("ws", .slice true .u64 "ws_len")]

/-- For `rounds` of 18 or 24 and a working space of at least `L.size` bytes
whose table encodes some words of `rounds` rounds in the order of some
direction (as `vg_camellia_prepare_keys` leaves it): wherever the table
encodes the words `w` of `rounds` rounds in the order of the direction `d`,
the `L.blocks` blocks at `L.buf` are replaced by their ECB in direction `d`
under the subkeys of `rounds` rounds of those words,
`subkeysOfWords rounds w`. Only the bytes of `L.cryptScratch` change. -/
def cryptContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  cryptSig.contract A
    (pre := fun rounds ws wsLen m => (rounds.toNat = 18 ∨ rounds.toNat = 24) ∧ L.size ≤ 8 * wsLen.toNat ∧
      ∃ w d, Holds L m ws rounds.toNat w d)
    (post := fun rounds ws wsLen m m' _ =>
      (∀ w d, Holds L m ws rounds.toNat w d →
        blocksAt m' (ws + BitVec.ofNat 64 L.buf) L.blocks =
          ecb (subkeysOfWords rounds.toNat w) d (blocksAt m (ws + BitVec.ofNat 64 L.buf) L.blocks)) ∧
      Keeps ws wsLen.toNat L.cryptScratch m m')
    (stack := stack)

/-! ## Encryption only: the preparation -/

/-- `vg_camellia_prepare_encrypt_keys(schedule, rounds, ws, ws_len)`: the
subkeys, the number of rounds, public, and the working space, in 64-bit
words. -/
def prepareEncryptSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("ws", .slice true .u64 "ws_len")]

/-- For `rounds` of 18 or 24 and a working space of at least `L.size`
bytes: the table encodes the words of the subkeys of `rounds` rounds at
`schedule` in the order of encryption. Only the bytes of `L.prepScratch`
change. -/
def prepareEncryptContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  prepareEncryptSig.contract A
    (pre := fun _schedule rounds _ws wsLen _ =>
      (rounds.toNat = 18 ∨ rounds.toNat = 24) ∧ L.size ≤ 8 * wsLen.toNat)
    (post := fun schedule rounds ws wsLen m m' _ =>
      Holds L m' ws rounds.toNat (wordsAt m schedule rounds.toNat) .encrypt ∧
        Keeps ws wsLen.toNat L.prepScratch m m')
    (stack := stack)

/-! ## Encryption only: a batch -/

/-- For `rounds` of 18 or 24 and a working space of at least `L.size` bytes
whose table encodes some words of `rounds` rounds in the order of
encryption (as `vg_camellia_prepare_encrypt_keys` leaves it): wherever the
table encodes the words `w` of `rounds` rounds in that order, the
`L.blocks` blocks at `L.buf` are replaced by their ECB encryption under the
subkeys of `rounds` rounds of those words, `subkeysOfWords rounds w`. Only
the bytes of `L.cryptScratch` change. Its signature is
`vg_camellia_crypt_prepared`'s, `cryptSig`. -/
def encryptPreparedContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  cryptSig.contract A
    (pre := fun rounds ws wsLen m => (rounds.toNat = 18 ∨ rounds.toNat = 24) ∧ L.size ≤ 8 * wsLen.toNat ∧
      ∃ w, Holds L m ws rounds.toNat w .encrypt)
    (post := fun rounds ws wsLen m m' _ =>
      (∀ w, Holds L m ws rounds.toNat w .encrypt →
        blocksAt m' (ws + BitVec.ofNat 64 L.buf) L.blocks =
          ecb (subkeysOfWords rounds.toNat w) .encrypt (blocksAt m (ws + BitVec.ofNat 64 L.buf) L.blocks)) ∧
      Keeps ws wsLen.toNat L.cryptScratch m m')
    (stack := stack)

end VG.Proof.Camellia.Prepared
