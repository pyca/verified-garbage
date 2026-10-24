module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# What the modes need of a block cipher's core, on PPC64LE

A core (`Impl.Modes.PPC64LE.Core`) is a cipher's code for `G` blocks of `bw`
words at once, which the modes inline: `prepare` makes the key ready in the
core's slots of the scratch buffer at `sb`, and `crypt` encrypts the blocks
of its buffer. `CoreSpec c` is what the modes' proofs use of `c`, and
nothing else: the modes are proven once, for any core, and each cipher
proves `CoreSpec` of its own.

* `KeyArgs s rs k`: the key argument (in `r3`) in the state `s` gives the
  key `k`. It survives what a mode does before `prepare`
  (`keyArgs_congr`): keeping `r3` and the other registers the caller
  expects preserved but the mode's `r29`–`r31` (`KeptBut`), the regions,
  the statics' addresses, and memory outside `rs`, writable regions. (A key with more than one
  argument may thus keep the others in callee-saved registers.)
* `Ready s B ws k`: the key `k` is ready in `s`, with the scratch buffer at
  `B`, for a mode that writes within the regions `ws` (its data and the
  scratch buffer). It survives what a mode does between the core's code
  (`ready_frame`): keeping `r3` and the regions, and writing memory within
  `ws` outside the core's slots or within its buffer. (A core may thus read
  its key in place, apart from `ws`, rather than copy it.)
* `prepare_wp`, `crypt_wp`: each changes only the core's slots in memory,
  and keeps `sb`, `r3` and the registers the caller expects preserved
  (`kept`); every other register (and the link register) may change.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- The registers a core keeps for the mode, besides `sb`: the key's
argument, and every register the caller expects preserved (among them
`r29`–`r31`, which hold the mode's state). -/
def kept : List Reg := .r3 :: preserved

/-- `s'` has the registers of `kept` that `s` has, but the mode's
`r29`–`r31`: what a mode keeps around the core's code. -/
def KeptBut (s s' : State) : Prop := ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s'.gpr r = s.gpr r

theorem KeptBut.r3 {s s' : State} (h : KeptBut s s') : s'.gpr .r3 = s.gpr .r3 :=
  h .r3 (by decide) (by decide) (by decide) (by decide)

/-- The scratch buffer of `n` slots at `B` is writable in `s`, and does not
wrap around. -/
structure ScrIn (s : State) (B : Addr) (n : Nat) : Prop where
  wr : (⟨B, 8 * n⟩ : Region) ∈ s.wr
  fit : B.toNat + 8 * n ≤ 2 ^ 64

/-- Slot `k` of the scratch buffer at `B`. -/
abbrev slotA (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (8 * k)

/-- The core's slots. -/
abbrev coreRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.slots⟩

/-- Block `j` of the core's buffer. -/
abbrev blkAddr (c : Core) (B : Addr) (j : Nat) : Addr := slotA B c.buf + BitVec.ofNat 64 (4 * c.bw * j)

/-- The core's buffer. -/
abbrev blkRegion (c : Core) (B : Addr) : Region := ⟨slotA B c.buf, 4 * c.bw * c.G⟩

/-- A core's layout: a buffer of at least one block within its slots, blocks
of 2 or 4 words, room for a mode's 6 slots after the core's, and a scratch
buffer the instructions' displacements reach. -/
structure Layout (c : Core) : Prop where
  G_pos : 0 < c.G
  bw : c.bw = 2 ∨ c.bw = 4
  buf_le : 8 * c.buf + 4 * c.bw * c.G ≤ 8 * c.slots
  room : c.slots + 6 ≤ c.total
  disp : 8 * c.total < 2 ^ 15

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → List Region → Key → Prop
  Ready : State → Addr → List Region → Key → Prop
  cipher_len : ∀ k b, (cipher k b).length = 4 * c.bw
  layout : Layout c
  keyArgs_congr : ∀ {s s' : State} {rs : List Region} {k : Key}, KeyArgs s rs k →
    KeptBut s s' → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Frame rs s.mem s'.mem →
    KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {ws : List Region} {k : Key} {rs : List Region},
    Ready s B ws k → KeptBut s s' → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)) → Ready s' B ws k
  prepare_wp : ∀ {s : State} {B : Addr} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B, 8 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    WP isa c.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion c B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {ws : List Region} {k : Key}, s.gpr sb = B → ScrIn s B c.total →
    Ready s B ws k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Ready s' B ws k ∧
      Frame [coreRegion c B] s.mem s'.mem ∧
      (∀ j < c.G, bytesAt s'.mem (blkAddr c B j) (4 * c.bw) =
        cipher k (bytesAt s.mem (blkAddr c B j) (4 * c.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

end VG.Proof.Modes.PPC64LE
