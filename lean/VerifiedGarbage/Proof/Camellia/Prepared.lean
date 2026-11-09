module
public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.TCB.Artifact

/-!
# Camellia with its subkeys prepared once, in a working space

Not trusted: the layout and the predicates in which the proofs of internal
functions (`Rust.Internal`), which only verified code calls, state what
those functions do, and which the proofs of their callers compose. Only the
callers' contracts, in `Spec/`, are trusted.

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
composed, so the encoding is the implementation's: whatever it is, what a
batch's proof shows holds only where the table encodes the subkeys of a
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

end VG.Proof.Camellia.Prepared
