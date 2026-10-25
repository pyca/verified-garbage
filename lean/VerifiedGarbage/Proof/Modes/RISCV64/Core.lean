module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# What the modes need of a block cipher's core, on RISC-V

A core (`Impl.Modes.RISCV64.Core`) is a cipher's code for `G` blocks of `bw`
words at once, which the modes inline: `prepare` makes the key ready in the
core's slots of the mode's frame at `sb`, and `crypt` encrypts the blocks
of its buffer. `CoreSpec c` is what the modes' proofs use of `c`, and
nothing else: the modes are proven once, for any core, and each cipher
proves `CoreSpec` of its own.

* `KeyArgs s rs k`: the key argument (in `a0`) in the state `s` gives the
  key `k`. It survives what a mode does before `prepare`
  (`keyArgs_congr`): keeping `a0` and the other registers the caller
  expects preserved but the mode's `s1`–`s4` (`KeptBut`), the readable
  regions, the writable regions the caller gave, and memory outside `rs`.
* `Ready s B ws k`: the key `k` is ready in `s`, with the frame at `B`, for
  a mode that writes within the regions `ws` (its data and the frame). It
  survives what a mode does between the core's code (`ready_frame`):
  keeping `a0`, the registers the caller expects preserved, the regions,
  and writing memory within `ws` outside the core's slots or within its
  buffer.
* `prepare_wp`, `crypt_wp`: each changes only the core's slots in memory,
  and keeps `sb`, `a0`, `ra` and the registers the caller expects
  preserved (`kept`); every other register may change.
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

/-- The registers a core keeps for the mode: the key's argument, `ra`, and
every register the caller expects preserved (among them `s1`–`s4`, which
hold the mode's state). -/
def kept : List Reg := .a0 :: .ra :: preserved

/-- `s'` has the registers of `kept` that `s` has, but the mode's
`s1`–`s4`: what a mode keeps around the core's code. -/
def KeptBut (s s' : State) : Prop :=
  ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s'.gpr r = s.gpr r

theorem KeptBut.a0 {s s' : State} (h : KeptBut s s') : s'.gpr .a0 = s.gpr .a0 :=
  h .a0 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The frame of `n` slots at `B` in `s`: 16-byte aligned, not wrapping
around, its lowest 2032 bytes (or all of it) one writable region, and the
rest writable an access within a 16-byte aligned chunk at a time. -/
structure ScrIn (s : State) (B : Addr) (n : Nat) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 8 * n ≤ 2 ^ 64
  low : (⟨B, min (8 * n) 2032⟩ : Region) ∈ s.wr
  wr : ∀ o w, 0 < w → o + w ≤ 8 * n → o % 16 + w ≤ 16 → InRegions s.wr (B + BitVec.ofNat 64 o) w

theorem ScrIn.congr {s s' : State} {B : Addr} {n : Nat} (h : ScrIn s B n) (hw : s'.wr = s.wr) :
    ScrIn s' B n :=
  ⟨h.al, h.fit, by rw [hw]; exact h.low, by rw [hw]; exact h.wr⟩

/-- Slot `k` of the frame at `B`. -/
abbrev slotA (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (8 * k)

/-- The core's slots. -/
abbrev coreRegion (c : Core) (B : Addr) : Region := ⟨slotA B coreSlot, 8 * (c.total - coreSlot)⟩

/-- Block `j` of the core's buffer. -/
abbrev blkAddr (c : Core) (B : Addr) (j : Nat) : Addr := slotA B c.buf + BitVec.ofNat 64 (4 * c.bw * j)

/-- The core's buffer. -/
abbrev blkRegion (c : Core) (B : Addr) : Region := ⟨slotA B c.buf, 4 * c.bw * c.G⟩

/-- A core's layout: a buffer of at least one block within its slots, which
the instructions' displacements reach and the frame's lowest region holds,
blocks of 2 or 4 words, and a frame
of an even number of slots, which `li` can count. -/
structure Layout (c : Core) : Prop where
  G_pos : 0 < c.G
  bw : c.bw = 2 ∨ c.bw = 4
  buf_ge : coreSlot ≤ c.buf
  buf_le : 8 * c.buf + 4 * c.bw * c.G ≤ 8 * c.total
  disp : 8 * c.buf + 4 * c.bw * c.G ≤ 2032
  even : c.total % 2 = 0
  total : c.total < 2048

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → List Region → Key → Prop
  Ready : State → Addr → List Region → Key → Prop
  cipher_len : ∀ k b, (cipher k b).length = 4 * c.bw
  layout : Layout c
  keyArgs_congr : ∀ {s s' : State} {rs : List Region} {k : Key}, KeyArgs s rs k →
    KeptBut s s' → s'.rd = s.rd → (∃ ws, s'.wr = ws ++ s.wr) → Frame rs s.mem s'.mem →
    KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {ws : List Region} {k : Key} {rs : List Region},
    Ready s B ws k → KeptBut s s' → s'.rd = s.rd → s'.wr = s.wr → Frame rs s.mem s'.mem →
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

end VG.Proof.Modes.RISCV64
