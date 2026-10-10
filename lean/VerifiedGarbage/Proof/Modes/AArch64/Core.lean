import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Spec.Cbc

/-!
# What the modes need of a block cipher's core, on AArch64

As on x86-64 (`Proof/Modes/X86_64/Core.lean`). A core
(`Impl.Modes.AArch64.Core`) is a cipher's code for many blocks at once,
which the modes inline: `prepare` makes the key ready in the core's slots
of the scratch buffer at `sb`, and `crypt` encrypts the `G` blocks of its
buffer. `CoreSpec c` is what each mode's proof uses of `c`, and nothing
else: the modes are proven once, for any core, and each cipher proves
`CoreSpec` of its own.

* `KeyArgs s rs k`: the key arguments in the state `s` (e.g. the schedule's
  address in `x0`) give the key `k`, which lies outside the regions `rs`
  (the scratch buffer among them). It survives what a mode does before
  `prepare` (`keyArgs_congr`): changing no register of `keyRegs`, nothing
  outside `rs` in memory.
* `Ready s B k`: the key `k` is ready in the state `s`, with the scratch
  buffer at `B`. It depends only on the core's slots outside its buffer and
  on the registers the modes do not write (`modeRegs`, `ready_frame`), so a
  core may keep part of it in registers (e.g. a pointer to its table's
  end).
* `prepare_wp`, `crypt_wp`: with the scratch buffer of `total` slots, each
  changes only the core's slots in memory, and keeps `sb`, `dataReg` and
  `leftReg`; every other register may change. (No AArch64 instruction the
  model executes outside a frame changes the stack pointer: `Exec.sp`.)
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Spec.Aes (bytesAt)

/-- The scratch buffer of `n` slots at `B` is writable in `s`, and does not
wrap around. -/
structure ScrIn (s : State) (B : Addr) (n : Nat) : Prop where
  wr : (⟨B, 8 * n⟩ : Region) ∈ s.wr
  fit : B.toNat + 8 * n ≤ 2 ^ 64

/-- Block `j` of the core's buffer, with the scratch buffer at `B`. -/
abbrev bufAddr (c : Core) (B : Addr) (j : Nat) : Addr := B + BitVec.ofNat 64 (8 * c.buf + 16 * j)

/-- The core's slots. -/
abbrev coreRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.slots⟩

/-- The core's buffer. -/
abbrev bufRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.buf), 16 * c.G⟩

/-- A core's layout: a buffer within its slots, room for a mode's 12 slots
after them, the whole scratch buffer within reach of a load's offset and
the buffer of an `add`'s immediate, and `G` the immediate of a `movz`. -/
structure Layout (c : Core) : Prop where
  lgG_lt : c.lgG < 16
  buf_le : c.buf + 2 * c.G ≤ c.slots
  room : c.slots + 12 ≤ c.total
  small : 8 * c.total < 32768
  bufImm : 8 * c.buf < 4096

theorem Layout.G_pos {c : Core} (_ : Layout c) : 0 < c.G := Nat.two_pow_pos _

theorem Layout.G_lt {c : Core} (h : Layout c) : c.G < 2 ^ 16 := Nat.pow_lt_pow_right (by decide) h.lgG_lt

/-- The registers the modes write between the core's code: their own and
the two the core keeps for them. -/
def modeRegs (c : Core) : List Reg :=
  [.x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17, c.dataReg, c.leftReg]

/-- The modes' own registers. -/
def ownRegs : List Reg := [.x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17]

theorem of_not_modeRegs {c : Core} {r : Reg} (h : r ∉ modeRegs c) :
    r ∉ ownRegs ∧ r ≠ c.dataReg ∧ r ≠ c.leftReg := by
  simp only [modeRegs, ownRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11, h12⟩

/-- The registers a core keeps for a mode: neither among the modes' own,
`sb`, nor a key argument, nor the same. -/
def regsOk (c : Core) : Bool :=
  [c.dataReg, c.leftReg].all (fun r => !(ownRegs.contains r) && r != sb && !(c.keyRegs.contains r)) &&
    c.dataReg != c.leftReg

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → List Region → Key → Prop
  Ready : State → Addr → Key → Prop
  cipher_len : ∀ k b, (cipher k b).length = 16
  layout : Layout c
  keyRegs_ok : c.keyRegs.all (fun r => r != sb && r != .x6 && r != .x7 && r != .x10) = true
  regs_ok : regsOk c = true
  keyArgs_congr : ∀ {s s' : State} {rs : List Region} {k : Key}, KeyArgs s rs k →
    (∀ r ∈ c.keyRegs, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → Frame rs s.mem s'.mem →
    KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {k : Key} {rs : List Region}, Ready s B k → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (bufRegion c B)) →
    (∀ r, r ∉ modeRegs c → s'.gpr r = s.gpr r) → Ready s' B k
  prepare_wp : ∀ {s : State} {B : Addr} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B, 8 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    WP isa c.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧
      Frame [coreRegion c B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {k : Key}, s.gpr sb = B → ScrIn s B c.total → Ready s B k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧ Ready s' B k ∧
      Frame [coreRegion c B] s.mem s'.mem ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = cipher k (bytesAt s.mem (bufAddr c B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

/-- What `regsOk` says, one register at a time. -/
theorem regsOk_ne {c : Core} (h : regsOk c = true) :
    (∀ r ∈ [c.dataReg, c.leftReg], r ∉ ownRegs ∧ r ≠ sb ∧ r ∉ c.keyRegs) ∧ c.dataReg ≠ c.leftReg := by
  simp only [regsOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨fun r hr => ?_, h.2⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 r hr
  refine ⟨fun e => ?_, h2, fun e => ?_⟩
  · simp [e] at h1
  · simp [e] at h3

end VG.Proof.Modes.AArch64
