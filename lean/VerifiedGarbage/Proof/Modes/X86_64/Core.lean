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

* `KeyArgs s R k`: the key arguments in the state `s` (e.g. the schedule's
  address in `rdi`) give the key `k`, where `R` is the scratch buffer. It
  survives what a mode does before `prepare` (`keyArgs_congr`): changing
  no register of `keyRegs`, nothing outside `R` in memory.
* `Ready m B k`: the key `k` is ready in the memory `m` at `B`. It depends
  only on the core's slots outside its buffer (`ready_frame`).
* `prepare_wp`, `crypt_wp`: each changes only the core's slots in memory,
  and keeps `sb` and `rsp`; every other register may change.
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

/-- A core's layout: a buffer of at least one block within its slots, and
the slots of a mode after them within reach of a 32-bit displacement. -/
structure Layout (c : Core) : Prop where
  G_pos : 0 < c.G
  buf_le : c.buf + 2 * c.G ≤ c.slots
  small : 8 * (c.slots + 10) < 2 ^ 31

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  Key : Type
  cipher : Key → Spec.Cbc.Cipher
  KeyArgs : State → Region → Key → Prop
  Ready : Mem → Addr → Key → Prop
  layout : Layout c
  keyRegs_ok : c.keyRegs.all (fun r => r != .rax && r != .rbx && r != sb) = true
  keyArgs_congr : ∀ {s s' : State} {R : Region} {k : Key}, KeyArgs s R k →
    (∀ r ∈ c.keyRegs, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → Frame [R] s.mem s'.mem →
    KeyArgs s' R k
  ready_frame : ∀ {m m' : Mem} {B : Addr} {k : Key} {rs : List Region}, Ready m B k → Frame rs m m' →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (bufRegion c B)) → Ready m' B k
  prepare_wp : ∀ {s : State} {B : Addr} {n : Nat} {k : Key}, s.gpr sb = B → c.slots ≤ n → ScrIn s B n →
    KeyArgs s ⟨B, 8 * n⟩ k →
    WP isa c.prepare s fun s' => Ready s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [coreRegion c B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  crypt_wp : ∀ {s : State} {B : Addr} {n : Nat} {k : Key}, s.gpr sb = B → c.slots ≤ n → ScrIn s B n →
    Ready s.mem B k →
    WP isa c.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧ Ready s'.mem B k ∧
      Frame [coreRegion c B] s.mem s'.mem ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = cipher k (bytesAt s.mem (bufAddr c B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

end VG.Proof.Modes.X86_64
