import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Spec.Aes

/-!
# What the modes need of a block cipher's core, on x86 (32-bit)

A core (`Impl.Modes.X86.Core`) is a cipher's code for `G` blocks of `bw`
words at once, which the modes inline: `prepare` makes the key ready in the
core's slots of the scratch buffer at `sb`, and `crypt` encrypts the blocks
of its buffer. `CoreSpec c` is what the modes' proofs use of `c`, and
nothing else: the modes are proven once, for any core, and each cipher
proves `CoreSpec` of its own.

* `KeyArgs s rs k`: the key arguments in the state `s` (e.g. the schedule's
  address in a stack argument) give the key `k`. It survives what a mode
  does before `prepare` (`keyArgs_congr`): keeping `esp`, the regions, and
  memory outside `rs`, writable regions.
* `Ready s B k`: the key `k` is ready in `s`, with the scratch buffer at `B`.
  It survives what a mode does between the core's code (`ready_frame`):
  keeping `esp` and the regions, and writing writable memory outside the
  core's slots or within its buffer.
* `prepare_wp`, `crypt_wp`: each changes only the core's slots and the
  `stack` bytes below `esp` in memory, and keeps `sb` and `esp`; every other
  register may change.
-/

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

/-- The scratch buffer of `n` slots at `B` is writable in `s`, and does not
wrap around. -/
structure ScrIn (s : State) (B : BitVec 32) (n : Nat) : Prop where
  wr : (⟨B.setWidth 64, 4 * n⟩ : Region) ∈ s.wr
  fit : B.toNat + 4 * n ≤ 2 ^ 32

/-- Slot `k` of the scratch buffer at `B`. -/
abbrev slotA (B : BitVec 32) (k : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 (4 * k)

/-- The core's slots. -/
abbrev coreRegion (c : Core) (B : BitVec 32) : Region := ⟨B.setWidth 64, 4 * c.slots⟩

/-- Block `j` of the core's buffer. -/
abbrev blkAddr (c : Core) (B : BitVec 32) (j : Nat) : Addr := slotA B c.buf + BitVec.ofNat 64 (4 * c.bw * j)

/-- The core's buffer. -/
abbrev blkRegion (c : Core) (B : BitVec 32) : Region := ⟨slotA B c.buf, 4 * c.bw * c.G⟩

/-- The `n` bytes below `esp = E`. -/
abbrev stkRegion (E : BitVec 32) (n : Nat) : Region := ⟨(E - BitVec.ofNat 32 n).setWidth 64, n⟩

/-- A core's layout: a buffer of at least one block within its slots, blocks
of 2 or 4 words, and room for a mode's 10 slots after the core's. -/
structure Layout (c : Core) : Prop where
  G_pos : 0 < c.G
  bw : c.bw = 2 ∨ c.bw = 4
  buf_le : c.buf + c.bw * c.G ≤ c.slots
  room : c.slots + 10 ≤ c.total

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → List Region → Key → Prop
  Ready : State → BitVec 32 → Key → Prop
  cipher_len : ∀ k b, (cipher k b).length = 4 * c.bw
  layout : Layout c
  keyArgs_congr : ∀ {s s' : State} {rs : List Region} {k : Key}, KeyArgs s rs k →
    s'.gpr .esp = s.gpr .esp → s'.rd = s.rd → s'.wr = s.wr → Frame rs s.mem s'.mem →
    KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : BitVec 32} {k : Key} {rs : List Region}, Ready s B k →
    s'.gpr .esp = s.gpr .esp → s'.rd = s.rd → s'.wr = s.wr → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)) → Ready s' B k
  prepare_wp : ∀ {s : State} {B : BitVec 32} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B.setWidth 64, 4 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    c.stack ≤ (s.gpr .esp).toNat →
    WP isa c.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion c B, stkRegion (s.gpr .esp) c.stack] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : BitVec 32} {k : Key}, s.gpr sb = B → ScrIn s B c.total → Ready s B k →
    c.stack ≤ (s.gpr .esp).toNat →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion c B, stkRegion (s.gpr .esp) c.stack] s.mem s'.mem ∧
      (∀ j < c.G, bytesAt s'.mem (blkAddr c B j) (4 * c.bw) =
        cipher k (bytesAt s.mem (blkAddr c B j) (4 * c.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

end VG.Proof.Modes.X86
