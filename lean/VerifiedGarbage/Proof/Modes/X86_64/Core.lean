import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Spec.Cbc

/-!
# What the modes need of a block cipher's core, on x86-64

A core (`Impl.Modes.X86_64.Core`) is a cipher's code for many blocks at
once, which the modes inline: `prepare` makes the key ready in the core's
slots of the scratch buffer at `sb`, and `crypt` encrypts the `G` blocks of
its buffer. `CoreSpec c` is what each mode's proof uses of `c`, and nothing
else: the modes are proven once, for any core, and each cipher proves
`CoreSpec` of its own.

* `KeyArgs s rs k`: the key arguments in the state `s` (e.g. the schedule's
  address in `rdi`) give the key `k`, which lies outside the regions `rs`
  (the scratch buffer among them). It survives what a mode does before
  `prepare` (`keyArgs_congr`): changing no register of `keyRegs`, nothing
  outside `rs` in memory.
* `Ready s B k`: the key `k` is ready in the state `s`, with the scratch
  buffer at `B`. It depends only on the core's slots outside its buffer and
  on the registers the modes do not write (`modeRegs`, `ready_frame`), so a
  core may keep part of it in registers (e.g. a pointer it saves and
  restores around its rounds).
* `prepare_wp`, `crypt_wp`: with the scratch buffer of `total` slots, each
  changes only the core's slots in memory, and keeps `sb`, `rsp`,
  `dataReg` and `leftReg`; every other register may change.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb)
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

/-- A core's layout: a buffer of at least one block within its slots, room
for a mode's 8 slots after them, and the whole scratch buffer within reach
of a 32-bit displacement. -/
structure Layout (c : Core) : Prop where
  G_pos : 0 < c.G
  buf_le : c.buf + 2 * c.G ≤ c.slots
  room : c.slots + 8 ≤ c.total
  small : 8 * c.total < 2 ^ 31

/-- The registers the modes write between the core's code: their own
(`rax`, `rbx`, `rcx`, `rbp`, `r10`) and the two the core keeps for them. -/
def modeRegs (c : Core) : List Reg := [.rax, .rbx, .rcx, .rbp, .r10, c.dataReg, c.leftReg]

theorem not_modeRegs {c : Core} {r : Reg} (h1 : r ≠ .rax) (h2 : r ≠ .rbx) (h3 : r ≠ .rcx) (h4 : r ≠ .rbp)
    (h5 : r ≠ .r10) (h6 : r ≠ c.dataReg) (h7 : r ≠ c.leftReg) : r ∉ modeRegs c := by
  simp only [modeRegs, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> contradiction

theorem of_not_modeRegs {c : Core} {r : Reg} (h : r ∉ modeRegs c) :
    r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx ∧ r ≠ .rbp ∧ r ≠ .r10 ∧ r ≠ c.dataReg ∧ r ≠ c.leftReg := by
  simp only [modeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

/-- The registers a core keeps for a mode: neither among the registers the
modes use (`rax`, `rbx`, `rcx`, `rbp`, `r10`), `sb` or `rsp`, nor a key
argument, nor the same. -/
def regsOk (c : Core) : Bool :=
  [c.dataReg, c.leftReg].all (fun r => !([Reg.rax, .rbx, .rcx, .rbp, .r10, sb, .rsp].contains r) &&
    !(c.keyRegs.contains r)) && c.dataReg != c.leftReg

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → List Region → Key → Prop
  Ready : State → Addr → Key → Prop
  cipher_len : ∀ k b, (cipher k b).length = 16
  layout : Layout c
  keyRegs_ok : c.keyRegs.all (fun r => r != .rax && r != .rbx && r != sb) = true
  regs_ok : regsOk c = true
  keyArgs_congr : ∀ {s s' : State} {rs : List Region} {k : Key}, KeyArgs s rs k →
    (∀ r ∈ c.keyRegs, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → Frame rs s.mem s'.mem →
    KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {k : Key} {rs : List Region}, Ready s B k → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (bufRegion c B)) →
    (∀ r, r ∉ modeRegs c → s'.gpr r = s.gpr r) → Ready s' B k
  prepare_wp : ∀ {s : State} {B : Addr} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B, 8 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    WP isa c.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧
      Frame [coreRegion c B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {k : Key}, s.gpr sb = B → ScrIn s B c.total → Ready s B k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧ Ready s' B k ∧
      Frame [coreRegion c B] s.mem s'.mem ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = cipher k (bytesAt s.mem (bufAddr c B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

/-! ## Blocks of `bw` words, for CBC

CTR's counter blocks are 16 bytes, and `CoreSpec` states the core's blocks
as 16 bytes; CBC works on blocks of any `bw` words. `BlockSpec` is
`CoreSpec` with blocks of `8 bw` bytes, which a core of 16-byte blocks has
(`CoreSpec.toBlock`). -/

/-- Block `j` of the core's buffer, of `bw` words. -/
abbrev blkAddr (c : Core) (B : Addr) (j : Nat) : Addr := B + BitVec.ofNat 64 (8 * c.buf + 8 * c.bw * j)

/-- The core's buffer, of `G` blocks of `bw` words. -/
abbrev blkRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.buf), 8 * c.bw * c.G⟩

/-- `Layout` for blocks of `bw` words, at most the 2 of the chaining
value's slots. -/
structure BLayout (c : Core) : Prop where
  G_pos : 0 < c.G
  bw_pos : 0 < c.bw
  bw_le : c.bw ≤ 2
  buf_le : c.buf + c.bw * c.G ≤ c.slots
  room : c.slots + 8 ≤ c.total
  small : 8 * c.total < 2 ^ 31

/-- `CoreSpec` for blocks of `bw` words. -/
structure BlockSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → List Region → Key → Prop
  Ready : State → Addr → Key → Prop
  cipher_len : ∀ k b, (cipher k b).length = 8 * c.bw
  layout : BLayout c
  keyRegs_ok : c.keyRegs.all (fun r => r != .rax && r != .rbx && r != sb) = true
  regs_ok : regsOk c = true
  keyArgs_congr : ∀ {s s' : State} {rs : List Region} {k : Key}, KeyArgs s rs k →
    (∀ r ∈ c.keyRegs, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → Frame rs s.mem s'.mem →
    KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {k : Key} {rs : List Region}, Ready s B k → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)) →
    (∀ r, r ∉ modeRegs c → s'.gpr r = s.gpr r) → Ready s' B k
  prepare_wp : ∀ {s : State} {B : Addr} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B, 8 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    WP isa c.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧
      Frame [coreRegion c B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {k : Key}, s.gpr sb = B → ScrIn s B c.total → Ready s B k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧ Ready s' B k ∧
      Frame [coreRegion c B] s.mem s'.mem ∧
      (∀ j < c.G, bytesAt s'.mem (blkAddr c B j) (8 * c.bw) =
        cipher k (bytesAt s.mem (blkAddr c B j) (8 * c.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

/-- A core of 16-byte blocks, as one of blocks of `bw = 2` words. -/
def CoreSpec.toBlock {c : Core} (cs : CoreSpec c) (h : c.bw = 2) : BlockSpec c where
  Key := cs.Key
  cipher := cs.cipher
  KeyArgs := cs.KeyArgs
  Ready := cs.Ready
  cipher_len k b := by rw [h, cs.cipher_len]
  layout := ⟨cs.layout.G_pos, by omega, by omega, by have := cs.layout.buf_le; rw [h]; omega, cs.layout.room,
    cs.layout.small⟩
  keyRegs_ok := cs.keyRegs_ok
  regs_ok := cs.regs_ok
  keyArgs_congr := cs.keyArgs_congr
  ready_frame hr hf hd hg := cs.ready_frame hr hf (by simpa only [blkRegion, h] using hd) hg
  prepare_wp := cs.prepare_wp
  crypt_wp hB hs hr := WP.mono (cs.crypt_wp hB hs hr) fun _ ⟨b, sp, d, l, r, f, e, rd, wr⟩ =>
    ⟨b, sp, d, l, r, f, by simpa only [blkAddr, bufAddr, h] using e, rd, wr⟩

/-- What `regsOk` says, one register at a time. -/
theorem regsOk_ne {c : Core} (h : regsOk c = true) :
    (∀ r ∈ [c.dataReg, c.leftReg], r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx ∧ r ≠ .rbp ∧ r ≠ .r10 ∧ r ≠ sb ∧ r ≠ .rsp ∧
      r ∉ c.keyRegs) ∧ c.dataReg ≠ c.leftReg := by
  simp only [regsOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨fun r hr => ?_, h.2⟩
  have := h.1 r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> simp_all

end VG.Proof.Modes.X86_64
