module

public import VerifiedGarbage.Impl.Aes.AArch64.Sbox

/-!
# CTR on AArch64, for any block cipher with 16-byte blocks

`ctr core regs`: CTR over a block cipher's *core* (`Core`), the code that
encrypts a batch of `G = 2 ^ lgG` blocks at a time. The core is inlined: no
call is made, so a mode costs nothing over a cipher's own ECB. As on x86-64
(`Impl/Modes/X86_64/Ctr.lean`).

The scratch buffer is at `sb` (`x5`), of `core.total` slots: its first
`core.slots` are the core's, the next 12 the mode's (`savedSlot`, `hiSlot`,
`loSlot`). The core's contract (`Proof.Modes.AArch64.Core`) states what it
keeps: the scratch buffer's address, two registers of its choosing
(`dataReg`, `leftReg`), in which the mode keeps the data's address and the
blocks left, and its own slots' key material.

* The scratch buffer moves to `sb`, and the callee-saved registers are
  stored in the mode's slots.
* The counter block `T₁` is read as two big-endian 64-bit integers (`rev`)
  into the running counter's slots (`hiSlot`, `loSlot`), and the counter
  block to continue from, `T₁ + n mod 2¹²⁸`, is written back at once. The
  data's address and `n` move to `dataReg` and `leftReg`.
* `core.prepare` makes the key ready, from the key arguments (which the
  steps above leave alone: `core.keyRegs` are none of the registers they
  write).
* Each group of up to `G` blocks: the next `G` counter blocks to the core's
  buffer (`adds`, `adc` on the running counter, `rev` back to big-endian),
  `core.crypt` encrypts them in place, and the first `min(G, left)` are
  XORed into the data.

Only the pointers and `n` (and what is computed from them) are public; the
counter is secret like the key and the data, and no address or branch
depends on it. AArch64's taint analysis takes all memory, and the flags,
to be secret, so the public values stay in registers: the core keeps
`dataReg` and `leftReg`, and the group's count is chosen by a branch on
`leftReg >> lgG`, not by a conditional select.

The mode's own registers are `x6`–`x10` and `x13`–`x17` (`modeRegs`), which
a core may also use, but not to keep anything across the mode's code.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- A block cipher's core for the modes: with the scratch buffer of `total`
slots at `sb`, `prepare` makes the key, given by the registers `keyRegs`,
ready in the core's slots `[0, slots)`, and `crypt` replaces the `G`
16-byte blocks of the buffer at slot `buf` (`2 G` slots) with their
encryptions. Both keep `dataReg` and `leftReg`. A mode keeps its own slots
in `[slots, total)`. -/
structure Core where
  prepare : Prog isa
  crypt : Prog isa
  slots : Nat
  total : Nat
  buf : Nat
  lgG : Nat
  keyRegs : List Reg
  dataReg : Reg
  leftReg : Reg

/-- Where a mode's arguments are: the counter block's address, the data's
address, the number of blocks and the scratch buffer's address. -/
structure CtrRegs where
  ctr : Reg
  data : Reg
  n : Reg
  scr : Reg

namespace Core

variable (c : Core)

/-- The number of blocks the core encrypts at once. -/
def G : Nat := 2 ^ c.lgG

/-- The callee-saved registers, each kept in a slot of the mode. -/
def savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def savedSlot (i : Nat) : Nat := c.slots + i
def hiSlot : Nat := c.slots + 10
def loSlot : Nat := c.slots + 11

def saveRegs : List Instr := (List.range 10).map fun i => stS (c.savedSlot i) (savedRegs.getD i .x19)
def restoreRegs : List Instr := (List.range 10).map fun i => ldS (savedRegs.getD i .x19) (c.savedSlot i)

/-! ## The counter -/

/-- The scratch buffer to `sb`, the callee-saved registers to the mode's
slots. -/
def ctrEntry (r : CtrRegs) : List Instr := ([movR sb r.scr] : List Instr) ++ c.saveRegs

/-- The counter block at `r.ctr` to the running counter's slots, and `T₁ + n`
(`n` in `r.n`) back to `r.ctr`. -/
def ctrSetup (r : CtrRegs) : List Instr :=
  [.ldr .x .x6 r.ctr 0, .rev .x6 .x6, .ldr .x .x7 r.ctr 8, .rev .x7 .x7,
   stS c.hiSlot .x6, stS c.loSlot .x7,
   .movz .x .x10 0 0, .adds .x .x7 .x7 r.n, .adc .x .x6 .x6 .x10, .rev .x6 .x6, .rev .x7 .x7,
   .str .x .x7 r.ctr 8, .str .x .x6 r.ctr 0]

/-- The data's address and `n` to `dataReg` and `leftReg`. -/
def ctrArgs (r : CtrRegs) : List Instr := [movR c.dataReg r.data, movR c.leftReg r.n]

/-- Counter block `b` of the group (the running counter in `x6`, `x7`) to
block `b` of the buffer, and the running counter incremented (`x9 = 1`,
`x10 = 0`). -/
def ctrBlock (b : Nat) : List Instr :=
  [.rev .x8 .x6, stS (c.buf + 2 * b) .x8, .rev .x8 .x7, stS (c.buf + 2 * b + 1) .x8,
   .adds .x .x7 .x7 .x9, .adc .x .x6 .x6 .x10]

/-- The group's `G` counter blocks to the buffer, and the running counter
stepped by `G`. -/
def ctrBlocks : List Instr :=
  ([ldS .x6 c.hiSlot, ldS .x7 c.loSlot, .movz .x .x9 1 0, .movz .x .x10 0 0] : List Instr) ++
    (List.range c.G).flatMap c.ctrBlock ++ ([stS c.hiSlot .x6, stS c.loSlot .x7] : List Instr)

/-! ## The groups -/

/-- `x16 := min(left, G)`. -/
def groupCount : Prog isa :=
  .seq (.block [.lsr .x .x13 c.leftReg c.lgG])
    (.ite (.nonzero .x .x13) (.block [.movz .x .x16 (BitVec.ofNat 16 c.G) 0]) (.block [movR .x16 c.leftReg]))

/-- XOR `x17` blocks at `x14` into the blocks at `x15` (through `x8`, `x9`). -/
def xorBlocks : Prog isa :=
  .loop (.block [.ldr .x .x8 .x14 0, .ldr .x .x9 .x15 0, eorR .x8 .x8 .x9, .str .x .x8 .x15 0,
      .ldr .x .x8 .x14 8, .ldr .x .x9 .x15 8, eorR .x8 .x8 .x9, .str .x .x8 .x15 8,
      .addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1]) (.nonzero .x .x17)

/-- The buffer's address to `x14`, the data's to `x15`, the count to `x17`. -/
def xorArgs : List Instr :=
  [movR .x14 sb, .addImm .x .x14 .x14 (8 * c.buf), movR .x15 c.dataReg, movR .x17 .x16]

/-- On past the group's blocks. -/
def advance : List Instr := [movR c.dataReg .x15, .sub .x c.leftReg c.leftReg .x16]

/-- One group: its counter blocks, encrypted, XORed into the data. -/
def ctrGroup : Prog isa :=
  .seq (.block c.ctrBlocks) (.seq c.crypt (.seq c.groupCount (.seq (.block c.xorArgs)
    (.seq xorBlocks (.block c.advance)))))

/-- The whole function: the counter, the key, then the groups. -/
def ctr (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.ctrSetup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop c.ctrGroup (.nonzero .x c.leftReg)))
        (.block c.restoreRegs)))

end Core

end VG.Impl.Modes.AArch64
