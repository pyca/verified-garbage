module

public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4 with its round keys prepared once, in a working space

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

Two callable pieces of SM4's modes. A bitsliced implementation
turns the round keys into a table of its own (their bits as masks of its
lanes) before it transforms any block, at about the cost of a batch of
blocks: `vg_sm4_ecb` does so on every call. The modes transform one batch
at a time, so they prepare the table once, in their working space, with
`vg_sm4_prepare_keys`, and then transform each batch with
`vg_sm4_crypt_prepared`, which reads the table where the preparation wrote
it.

A `Layout`, which the implementation chooses for its working space, gives
the table's ranges and its encoding (`encode`): what
`vg_sm4_prepare_keys` writes there for the round keys in the order of a
direction, and what `vg_sm4_crypt_prepared` needs to find there to transform
its blocks in that direction. It also gives the offset of the batch's
`blocks` blocks, and the ranges each function may change. The two functions
are only ever composed, so the encoding is the implementation's: whatever
it is, the batch's postcondition holds only where the table encodes the
round keys of a direction, and then says that the batch is ECB in that
direction (`Spec/Sm4.lean`).

Every byte of the working space outside a function's ranges keeps its
value, so the table survives the batches, which do not change it. The
round keys, the table and the blocks are secret; the working space's
address and length, and the direction, are public.
-/

@[expose] public section

namespace VG.Proof.Sm4.Prepared

open VG.Spec VG.Spec.Sm4

/-- Where an implementation keeps the prepared round keys and the batch's
blocks in its working space, and how it encodes the round keys. -/
structure Layout where
  /-- The ranges `(offset, bytes)` of the working space that hold the
  prepared round keys. -/
  table : List (Nat × Nat)
  /-- The byte at an offset of those ranges, for the round keys `k` in the
  order of the direction. -/
  encode : Schedule → Direction → Nat → Byte
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

/-- The table of the working space at `ws` encodes the round keys `k` in the
order of the direction `d`. -/
def Holds (L : Layout) (m : Mem) (ws : Addr) (k : Schedule) (d : Direction) : Prop :=
  ∀ r ∈ L.table, ∀ i < r.2, m (ws + BitVec.ofNat 64 (r.1 + i)) = L.encode k d (r.1 + i)

/-- Every byte of `ws` outside the ranges `rs` keeps its value. -/
def Keeps (ws : Addr) (wsLen : Nat) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-! ## The preparation -/

/-- `vg_sm4_prepare_keys(schedule, decrypt, ws, ws_len)`: the round keys, the
direction (0 to encrypt, 1 to decrypt, public) and the working space, in
64-bit words. -/
def prepareSig : Sig where
  params := [("schedule", .array false .u8 128), ("decrypt", .int .usize true), ("ws", .slice true .u64 "ws_len")]

/-- For `decrypt` of 0 or 1 and a working space of at least `L.size` bytes:
the table encodes the round keys at `schedule` in the order of the direction
`decrypt` selects. Only the bytes of `L.prepScratch` change. -/
def prepareContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  prepareSig.contract A
    (pre := fun _schedule decrypt _ws wsLen _ => decrypt.toNat ≤ 1 ∧ L.size ≤ 8 * wsLen.toNat)
    (post := fun schedule decrypt ws wsLen m m' _ =>
      Holds L m' ws (scheduleAt m schedule) (directionOf decrypt.toNat) ∧
        Keeps ws wsLen.toNat L.prepScratch m m')
    (stack := stack)

/-! ## A batch -/

/-- `vg_sm4_crypt_prepared(ws, ws_len)`: the working space, in 64-bit words. -/
def cryptSig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]

/-- For a working space of at least `L.size` bytes whose table encodes some
round keys in the order of some direction (as `vg_sm4_prepare_keys` leaves
it): wherever the table encodes the round keys `k` in the order of the
direction `d`, the `L.blocks` blocks at `L.buf` are replaced by their ECB in
direction `d` under `k`. Only the bytes of `L.cryptScratch` change. -/
def cryptContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  cryptSig.contract A
    (pre := fun ws wsLen m => L.size ≤ 8 * wsLen.toNat ∧ ∃ k d, Holds L m ws k d)
    (post := fun ws wsLen m m' _ =>
      (∀ k d, Holds L m ws k d →
        blocksAt m' (ws + BitVec.ofNat 64 L.buf) L.blocks = ecb k d (blocksAt m (ws + BitVec.ofNat 64 L.buf) L.blocks)) ∧
      Keeps ws wsLen.toNat L.cryptScratch m m')
    (stack := stack)

end VG.Proof.Sm4.Prepared
