module

import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

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
  buffer at `B`. It depends only on the core's slots outside its buffer, on
  memory outside every writable region, on the statics' addresses, and on
  the registers the modes do not write (`modeRegs`, `ready_frame`, `WrIn`),
  so a core may keep part of it in registers (e.g. a pointer it saves and
  restores around its rounds), read a key too large for its slots where the
  caller passed it, or read a table among the statics.
* `prepare_wp`, `crypt_wp`: with the scratch buffer of `total` slots, each
  changes only the core's slots in memory, and the `stack` bytes below `rsp`
  (`coreFrame`), and keeps `sb`, `rsp`,
  `dataReg` and `leftReg`; every other register may change.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Spec.Aes (bytesAt)

/-- The scratch buffer of `n` slots at `B` is writable in `s`, and does not
wrap around. -/
structure ScrIn (s : State) (B : Addr) (n : Nat) : Prop where
  wr : (⟨B, 8 * n⟩ : Region) ∈ s.wr
  fit : B.toNat + 8 * n ≤ 2 ^ 64

/-- A straight-line block names the same addresses of statics after it as before. -/
theorem runBlock_syms : ∀ {is : List Instr} {s s' : State}, runBlock isa is s = some s' → s'.syms = s.syms
  | [], _, _, h => by cases h; rfl
  | i :: is, s, s', h => by
    obtain ⟨s₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    exact (runBlock_syms h₂).trans (exec_syms h₁)

/-- What the modes did between two states: written only within the writable
regions `rs`, which with the readable ones and the statics' addresses have
not changed. -/
structure WrIn (rs : List Region) (s s' : State) : Prop where
  sub : ∀ r ∈ rs, ∃ w ∈ s.wr, Region.Sub r w
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

/-- Block `j` of the core's buffer, with the scratch buffer at `B`. -/
abbrev bufAddr (c : Core) (B : Addr) (j : Nat) : Addr := B + BitVec.ofNat 64 (8 * c.buf + 16 * j)

/-- The core's slots. -/
abbrev coreRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.slots⟩

/-- The core's buffer. -/
abbrev bufRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.buf), 16 * c.G⟩

/-- The `n` bytes below `rsp`. -/
abbrev stkRegion (rsp : Addr) (n : Nat) : Region := ⟨rsp - BitVec.ofNat 64 n, n⟩

/-- The stack the core's code uses below `rsp`: none for a core of no
stack, so that its frame is its slots alone (`coreFrame`). -/
def stkList (c : Core) (rsp : Addr) : List Region := if c.stack = 0 then [] else [stkRegion rsp c.stack]

/-- What the core's code may write, with `rsp` as on entry: its slots and its stack. -/
abbrev coreFrame (c : Core) (B rsp : Addr) : List Region := coreRegion c B :: stkList c rsp

/-- The core uses no stack, or its stack (below `rsp` in `s`, which does not
wrap around) is apart from the writable regions of `s`. -/
def StkOk (c : Core) (s : State) : Prop :=
  c.stack = 0 ∨ (c.stack ≤ (s.gpr .rsp).toNat ∧ ∀ w ∈ s.wr, Region.Disjoint (stkRegion (s.gpr .rsp) c.stack) w)

/-- A core of no stack writes none. -/
theorem stkList_eq_nil {c : Core} (h : c.stack = 0) (rsp : Addr) : stkList c rsp = [] := by
  simp only [stkList, h, ↓reduceIte]

theorem mem_stkList {c : Core} {rsp : Addr} {r : Region} (h : r ∈ stkList c rsp) :
    c.stack ≠ 0 ∧ r = stkRegion rsp c.stack := by
  unfold stkList at h
  split at h
  · exact absurd h List.not_mem_nil
  · rename_i h0; exact ⟨h0, List.mem_singleton.mp h⟩

theorem StkOk.congr {c : Core} {s s' : State} (h : StkOk c s) (hrsp : s'.gpr .rsp = s.gpr .rsp)
    (hwr : s'.wr = s.wr) : StkOk c s' := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨by rw [hrsp]; exact h1, by rw [hrsp, hwr]; exact h2⟩

/-- A region within a writable region is apart from the core's stack. -/
theorem StkOk.disj {c : Core} {s : State} (h : StkOk c s) {R : Region} (hR : ∃ w ∈ s.wr, Region.Sub R w) :
    ∀ r ∈ stkList c (s.gpr .rsp), Region.Disjoint R r := fun r hr => by
  obtain ⟨h0, rfl⟩ := mem_stkList hr
  rcases h with h | ⟨-, h2⟩
  · exact absurd h h0
  · obtain ⟨w, hw, hs⟩ := hR
    exact ((h2 w hw).sub_right hs).symm

/-- A region apart from the core's slots and its stack is apart from its frame. -/
theorem coreFrame_disj {c : Core} {B rsp : Addr} {R : Region} (hc : Region.Disjoint R (coreRegion c B))
    (hs : ∀ r ∈ stkList c rsp, Region.Disjoint R r) : ∀ r ∈ coreFrame c B rsp, Region.Disjoint R r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hc
  · exact hs r hr

/-- A region within a writable region and apart from the core's slots is
apart from its frame. -/
theorem StkOk.coreFrame_disj {c : Core} {s : State} (h : StkOk c s) {B : Addr} {R : Region}
    (hc : Region.Disjoint R (coreRegion c B)) (hw : ∃ w ∈ s.wr, Region.Sub R w) :
    ∀ r ∈ coreFrame c B (s.gpr .rsp), Region.Disjoint R r :=
  VG.Proof.Modes.X86_64.coreFrame_disj hc (h.disj hw)

/-- The core's frame, within regions `rs` that contain its slots, and its stack. -/
theorem coreFrame_sub {c : Core} {B rsp : Addr} {rs : List Region} (h : ∃ r ∈ rs, Region.Sub (coreRegion c B) r) :
    ∀ r ∈ coreFrame c B rsp, ∃ r' ∈ rs ++ stkList c rsp, Region.Sub r r' := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · obtain ⟨r', h1, h2⟩ := h; exact ⟨r', List.mem_append_left _ h1, h2⟩
  · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

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
    (∀ r ∈ c.keyRegs, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
    Frame rs s.mem s'.mem → KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {k : Key} {rs : List Region}, Ready s B k → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (bufRegion c B)) → WrIn rs s s' →
    (∀ r, r ∉ modeRegs c → s'.gpr r = s.gpr r) → Ready s' B k
  prepare_wp : ∀ {s : State} {B : Addr} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B, 8 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    WP isa c.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧
      Frame (coreFrame c B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {k : Key}, s.gpr sb = B → ScrIn s B c.total → Ready s B k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧ Ready s' B k ∧
      Frame (coreFrame c B (s.gpr .rsp)) s.mem s'.mem ∧
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
    (∀ r ∈ c.keyRegs, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
    Frame rs s.mem s'.mem → KeyArgs s' rs k
  ready_frame : ∀ {s s' : State} {B : Addr} {k : Key} {rs : List Region}, Ready s B k → Frame rs s.mem s'.mem →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)) → WrIn rs s s' →
    (∀ r, r ∉ modeRegs c → s'.gpr r = s.gpr r) → Ready s' B k
  prepare_wp : ∀ {s : State} {B : Addr} {rs : List Region} {k : Key}, s.gpr sb = B →
    ScrIn s B c.total → (⟨B, 8 * c.total⟩ : Region) ∈ rs → KeyArgs s rs k →
    WP isa c.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧
      Frame (coreFrame c B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {k : Key}, s.gpr sb = B → ScrIn s B c.total → Ready s B k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr c.dataReg = s.gpr c.dataReg ∧ s'.gpr c.leftReg = s.gpr c.leftReg ∧ Ready s' B k ∧
      Frame (coreFrame c B (s.gpr .rsp)) s.mem s'.mem ∧
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
  ready_frame hr hf hd hw hg := cs.ready_frame hr hf (by simpa only [blkRegion, h] using hd) hw hg
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
