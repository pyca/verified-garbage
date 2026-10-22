module

public import VerifiedGarbage.Impl.Modes.AArch64.Ctr

/-!
# Counter mode with GCM's `inc₃₂` on AArch64, for any block cipher with 16-byte blocks

`ctr32 core regs`: CTR (`Ctr.lean`) with GCM's increment, `inc₃₂`, which
steps only the rightmost 32 bits of the counter block, modulo 2³², and
leaves the leftmost 96 as they are (NIST SP 800-38D §6.2). Everything but
the counter is `ctr`'s: the same entry, key, groups, XOR and exit, over the
same core. As on x86-64 (`Impl/Modes/X86_64/Ctr32.lean`).

* The counter block `CB₁` is read as two big-endian 64-bit integers into
  the running counter's slots, as `ctr` does, and `inc₃₂ⁿ(CB₁)` is written
  back at once.
* Each counter block of a group goes to the core's buffer as `ctr`'s does,
  and the running counter is stepped by `inc₃₂`: the low 32 bits of its low
  half (`x7`) incremented by a 32-bit `add` (which zero-extends) into a
  temporary, and added back to the low half cleared of them (`lsr`, `lsl` by 32).

The counter is secret like the key and the data: no address or branch
depends on it.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

namespace Core

variable (c : Core)

/-- `x7 := inc₃₂` of `x7` by the low 32 bits of `k`: its low 32 bits plus
`k`, modulo 2³², in `t`, added to its high 32 bits. -/
def inc32By (t k : Reg) : List Instr :=
  [.add .w t .x7 k, .lsr .x .x7 .x7 32, .lsl .x .x7 .x7 32, .add .x .x7 .x7 t]

/-- The counter block at `r.ctr` to the running counter's slots, and
`inc₃₂ⁿ(CB₁)` (`n` in `r.n`) back to `r.ctr` (through `x10`, as `ctrSetup`). -/
def ctr32Setup (r : CtrRegs) : List Instr :=
  [.ldr .x .x6 r.ctr 0, .rev .x6 .x6, .ldr .x .x7 r.ctr 8, .rev .x7 .x7,
   stS c.hiSlot .x6, stS c.loSlot .x7] ++ inc32By .x10 r.n ++
  [.rev .x6 .x6, .rev .x7 .x7, .str .x .x7 r.ctr 8, .str .x .x6 r.ctr 0]

/-- Counter block `b` of the group (the running counter in `x6`, `x7`) to
block `b` of the buffer, and the running counter stepped by `inc₃₂`
(`x9 = 1`). -/
def ctr32Block (b : Nat) : List Instr :=
  [.rev .x8 .x6, stS (c.buf + 2 * b) .x8, .rev .x8 .x7, stS (c.buf + 2 * b + 1) .x8] ++ inc32By .x8 .x9

/-- The group's `G` counter blocks to the buffer, and the running counter
stepped by `inc₃₂ᴳ`. -/
def ctr32Blocks : List Instr :=
  ([ldS .x6 c.hiSlot, ldS .x7 c.loSlot, .movz .x .x9 1 0] : List Instr) ++
    (List.range c.G).flatMap c.ctr32Block ++ ([stS c.hiSlot .x6, stS c.loSlot .x7] : List Instr)

/-- One group: its counter blocks, encrypted, XORed into the data. -/
def ctr32Group : Prog isa :=
  .seq (.block c.ctr32Blocks) (.seq c.crypt (.seq c.groupCount (.seq (.block c.xorArgs)
    (.seq xorBlocks (.block c.advance)))))

/-- The whole function: the counter, the key, then the groups. -/
def ctr32 (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.ctr32Setup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop c.ctr32Group (.nonzero .x c.leftReg)))
        (.block c.restoreRegs)))

end Core

end VG.Impl.Modes.AArch64
