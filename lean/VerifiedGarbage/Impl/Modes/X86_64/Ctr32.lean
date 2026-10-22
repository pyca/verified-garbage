module

public import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# Counter mode with GCM's `inc₃₂` on x86-64, for any block cipher with 16-byte blocks

`ctr32 core regs`: CTR (`Ctr.lean`) with GCM's increment, `inc₃₂`, which
steps only the rightmost 32 bits of the counter block, modulo 2³², and
leaves the leftmost 96 as they are (NIST SP 800-38D §6.2). Everything but
the counter is `ctr`'s: the same entry, key, groups, XOR and exit, over the
same core.

* The counter block `CB₁` is read as two big-endian 64-bit integers into
  the running counter's slots, as `ctr` does, and `inc₃₂ⁿ(CB₁)` is written
  back at once.
* Each counter block of a group goes to the core's buffer as `ctr`'s does,
  and the running counter is stepped by `inc₃₂`: the low 32 bits of its low
  half incremented in a 32-bit register (`add r32`, which zero-extends) and
  added back to the low half cleared of them (`shr`, `shl` by 32).
  At the entry the 32-bit register is `rax`, whose high half is reloaded
  from its slot after, since `n` may be in `rcx`.

The counter is secret like the key and the data: no address or branch
depends on it.
-/

@[expose] public section

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

namespace Core

variable (c : Core)

/-- `rbx := inc₃₂` of `rbx` by the 32-bit source `k`: its low 32 bits
plus `k`, modulo 2³², in `t`, added to its high 32 bits. -/
def inc32By (t : Reg) (k : Src) : List Instr :=
  [.mov32 t (.reg .rbx), .alu32 .add t k, .shift .shr .rbx 32, .shift .shl .rbx 32,
   .alu .add .rbx (.reg t)]

/-- The counter block at `r.ctr` to the running counter's slots, and
`inc₃₂ⁿ(CB₁)` (`n` in `r.n`) back to `r.ctr` (`rax`, the step's temporary,
reloaded from its slot). -/
def ctr32Setup (r : CtrRegs) : List Instr :=
  [.mov .rax (.mem (at_ r.ctr 0)), .bswap .rax, .mov .rbx (.mem (at_ r.ctr 8)), .bswap .rbx,
   st c.hiSlot .rax, st c.loSlot .rbx] ++ inc32By .rax (.reg r.n) ++
  [movS .rax c.hiSlot, .bswap .rax, .bswap .rbx, .store (at_ r.ctr 8) .rbx, .store (at_ r.ctr 0) .rax]

/-- Counter block `b` of the group (the running counter in `rax`, `rbx`) to
block `b` of the buffer, and the running counter stepped by `inc₃₂`. -/
def ctr32Block (b : Nat) : List Instr :=
  [movR .rcx .rax, .bswap .rcx, st (c.buf + 2 * b) .rcx, movR .rcx .rbx, .bswap .rcx, st (c.buf + 2 * b + 1) .rcx] ++
    inc32By .rcx (.imm 1)

/-- The group's `G` counter blocks to the buffer, and the running counter
stepped by `inc₃₂ᴳ`. -/
def ctr32Blocks : List Instr :=
  ([movS .rax c.hiSlot, movS .rbx c.loSlot] : List Instr) ++ (List.range c.G).flatMap c.ctr32Block ++
    ([st c.hiSlot .rax, st c.loSlot .rbx] : List Instr)

/-- One group: its counter blocks, encrypted, XORed into the data. -/
def ctr32Group : Prog isa :=
  .seq (.block c.ctr32Blocks) (.seq c.crypt (.seq c.groupCount (.seq (.block c.xorArgs)
    (.seq xorBlocks (.block c.advance)))))

/-- The whole function: the counter, the key, then the groups. -/
def ctr32 (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.ctr32Setup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
        (.seq (.ite .e (.block []) (.loop c.ctr32Group .ne)) (.block c.restoreRegs))))

end Core

end VG.Impl.Modes.X86_64
