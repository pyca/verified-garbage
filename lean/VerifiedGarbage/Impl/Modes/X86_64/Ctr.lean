module

public import VerifiedGarbage.Impl.Aes.X86_64.Sbox

/-!
# CTR on x86-64, for any block cipher with 16-byte blocks

`ctr core regs`: CTR over a block cipher's *core* (`Core`), the code that
encrypts a batch of `G` blocks at a time. The core is inlined: no call is
made, so a mode costs nothing over a cipher's own ECB.

The scratch buffer is at `sb` (`r9`), of `core.total` slots: its first
`core.slots` are the core's, the next 8 the mode's (`savedSlot`, `hiSlot`,
`loSlot`). The core's contract (`Proof.Modes.X86_64.Core`) states what it
keeps: the scratch buffer's address, the stack pointer, two registers of
its choosing (`dataReg`, `leftReg`), in which the mode keeps the data's
address and the blocks left, and its own slots' key material.

* The scratch buffer moves to `sb`, and the callee-saved registers are
  stored in the mode's slots.
* The counter block `T₁` is read as two big-endian 64-bit integers
  (`bswap`) into the running counter's slots (`hiSlot`, `loSlot`), and the
  counter block to continue from, `T₁ + n mod 2¹²⁸`, is written back at
  once. The data's address and `n` move to `dataReg` and `leftReg`.
* `core.prepare` makes the key ready, from the key arguments (which the
  steps above leave alone: `core.keyRegs` are none of the registers they
  write).
* Each group of up to `G` blocks: the next `G` counter blocks to the core's
  buffer (`add`, `adc` on the running counter, `bswap` back to big-endian),
  `core.crypt` encrypts them in place, and the first `min(G, left)` are
  XORed into the data.

Only the pointers and `n` (and what is computed from them) are public; the
counter is secret like the key and the data, and no address or branch
depends on it.
-/

@[expose] public section

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

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
  G : Nat
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

/-- The callee-saved registers, each kept in a slot of the mode. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def savedSlot (i : Nat) : Nat := c.slots + i
def hiSlot : Nat := c.slots + 6
def loSlot : Nat := c.slots + 7
/-- The scratch buffer's size, in slots: the core's, with the mode's 8
among them. -/
def ctrSlots : Nat := c.total

def saveRegs : List Instr := (List.range 6).map fun i => st (c.savedSlot i) (savedRegs.getD i .rbx)
def restoreRegs : List Instr := (List.range 6).map fun i => movS (savedRegs.getD i .rbx) (c.savedSlot i)

/-! ## The counter -/

/-- The scratch buffer to `sb`, the callee-saved registers to the mode's
slots. -/
def ctrEntry (r : CtrRegs) : List Instr := ([movR sb r.scr] : List Instr) ++ c.saveRegs

/-- The counter block at `r.ctr` to the running counter's slots, and `T₁ + n`
(`n` in `r.n`) back to `r.ctr`. -/
def ctrSetup (r : CtrRegs) : List Instr :=
  [.mov .rax (.mem (at_ r.ctr 0)), .bswap .rax, .mov .rbx (.mem (at_ r.ctr 8)), .bswap .rbx,
   st c.hiSlot .rax, st c.loSlot .rbx,
   .alu .add .rbx (.reg r.n), .alu .adc .rax (.imm 0), .bswap .rax, .bswap .rbx,
   .store (at_ r.ctr 8) .rbx, .store (at_ r.ctr 0) .rax]

/-- The data's address and `n` to `dataReg` and `leftReg`. -/
def ctrArgs (r : CtrRegs) : List Instr := [movR c.dataReg r.data, movR c.leftReg r.n]

/-- Counter block `b` of the group (the running counter in `rax`, `rbx`) to
block `b` of the buffer, and the running counter incremented. -/
def ctrBlock (b : Nat) : List Instr :=
  [movR .rcx .rax, .bswap .rcx, st (c.buf + 2 * b) .rcx, movR .rcx .rbx, .bswap .rcx, st (c.buf + 2 * b + 1) .rcx,
   .alu .add .rbx (.imm 1), .alu .adc .rax (.imm 0)]

/-- The group's `G` counter blocks to the buffer, and the running counter
stepped by `G`. -/
def ctrBlocks : List Instr :=
  ([movS .rax c.hiSlot, movS .rbx c.loSlot] : List Instr) ++ (List.range c.G).flatMap c.ctrBlock ++
    ([st c.hiSlot .rax, st c.loSlot .rbx] : List Instr)

/-! ## The groups -/

/-- `rcx := min(left, G)`. -/
def groupCount : Prog isa :=
  .seq (.block [.movImm64 .rcx (BitVec.ofNat 64 c.G), .alu .cmp c.leftReg (.imm (BitVec.ofNat 32 c.G))])
    (.ite .b (.block [movR .rcx c.leftReg]) (.block []))

/-- XOR `rcx` blocks at `rax` into the blocks at `rbx` (through `rbp`). -/
def xorBlocks : Prog isa :=
  .loop (.block [.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)]) .ne

/-- The buffer's address to `rax`, the data's to `rbx`, the count to `r10`. -/
def xorArgs : List Instr :=
  [movR .rax sb, .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf))), movR .rbx c.dataReg, movR .r10 .rcx]

/-- On past the group's blocks; ZF is set when none are left. -/
def advance : List Instr := [movR c.dataReg .rbx, .alu .sub c.leftReg (.reg .r10)]

/-- One group: its counter blocks, encrypted, XORed into the data. -/
def ctrGroup : Prog isa :=
  .seq (.block c.ctrBlocks) (.seq c.crypt (.seq c.groupCount (.seq (.block c.xorArgs)
    (.seq xorBlocks (.block c.advance)))))

/-- The whole function: the counter, the key, then the groups. -/
def ctr (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.ctrSetup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
        (.seq (.ite .e (.block []) (.loop c.ctrGroup .ne)) (.block c.restoreRegs))))

end Core

end VG.Impl.Modes.X86_64
