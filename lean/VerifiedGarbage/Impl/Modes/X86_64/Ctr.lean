import VerifiedGarbage.Impl.Aes.X86_64.Sbox

/-!
# CTR on x86-64, for any block cipher with 16-byte blocks

`ctr core regs`: CTR over a block cipher's *core* (`Core`), the code that
encrypts a batch of `G` blocks at a time. The core is inlined: no call is
made, so a mode costs nothing over a cipher's own ECB.

The scratch buffer is at `sb` (`r9`): its first `core.slots` slots are the
core's, the next 10 the mode's (`savedSlot`, `hiSlot`, …). The core's
contract (`Proof.Modes.X86_64.Core`) states what it keeps: the scratch
buffer's address, the stack pointer and its own slots' key material, and
nothing else, so the mode keeps its state in its slots across `crypt`.

* The scratch buffer moves to `sb`; the callee-saved registers, the counter
  block's address, the data's address and `n` are stored in the mode's
  slots.
* The counter block `T₁` is read as two big-endian 64-bit integers
  (`bswap`) into the running counter's slots (`hiSlot`, `loSlot`), and the
  counter block to continue from, `T₁ + n mod 2¹²⁸`, is written back at
  once.
* `core.prepare` makes the key ready, from the key arguments (which the
  steps above leave alone: `core.keyRegs` are none of the registers they
  write).
* Each group of up to `G` blocks: the next `G` counter blocks to the core's
  buffer (`add`, `adc` on the running counter, `bswap` back to big-endian),
  `core.crypt` encrypts them in place, and the first `min(G, left)` are
  XORed into the data.

Only the pointers and `n` (and what is computed from them: the data's
address and the blocks left, kept in the mode's slots) are public; the
counter is secret like the key and the data, and no address or branch
depends on it.
-/

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- A block cipher's core for the modes: with the scratch buffer at `sb`,
`prepare` makes the key, given by the registers `keyRegs`, ready in the
core's slots `[0, slots)`, and `crypt` replaces the `G` 16-byte blocks of
the buffer at slot `buf` (`2 G` slots) with their encryptions. -/
structure Core where
  prepare : Prog isa
  crypt : Prog isa
  slots : Nat
  buf : Nat
  G : Nat
  keyRegs : List Reg

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
def dataSlot : Nat := c.slots + 8
def leftSlot : Nat := c.slots + 9
/-- The scratch buffer's size, in slots: the core's and the mode's. -/
def ctrSlots : Nat := c.slots + 10

def saveRegs : List Instr := (List.range 6).map fun i => st (c.savedSlot i) (savedRegs.getD i .rbx)
def restoreRegs : List Instr := (List.range 6).map fun i => movS (savedRegs.getD i .rbx) (c.savedSlot i)

/-! ## The counter -/

/-- The scratch buffer to `sb`, the callee-saved registers and the data's
address and `n` to the mode's slots. -/
def ctrEntry (r : CtrRegs) : List Instr :=
  ([movR sb r.scr] : List Instr) ++ c.saveRegs ++ ([st c.dataSlot r.data, st c.leftSlot r.n] : List Instr)

/-- The counter block at `r.ctr` to the running counter's slots, and `T₁ + n`
(`n` in `r.n`) back to `r.ctr`. -/
def ctrSetup (r : CtrRegs) : List Instr :=
  [.mov .rax (.mem (at_ r.ctr 0)), .bswap .rax, .mov .rbx (.mem (at_ r.ctr 8)), .bswap .rbx,
   st c.hiSlot .rax, st c.loSlot .rbx,
   .alu .add .rbx (.reg r.n), .alu .adc .rax (.imm 0), .bswap .rax, .bswap .rbx,
   .store (at_ r.ctr 8) .rbx, .store (at_ r.ctr 0) .rax]

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

/-- `rcx := min(left, G)`, with the blocks left in `rdx`. -/
def groupCount : Prog isa :=
  .seq (.block [movS .rdx c.leftSlot, .movImm64 .rcx (BitVec.ofNat 64 c.G), .alu .cmp .rdx (.imm (BitVec.ofNat 32 c.G))])
    (.ite .b (.block [movR .rcx .rdx]) (.block []))

/-- XOR `rcx` blocks at `rax` into the blocks at `rbx` (through `rbp`). -/
def xorBlocks : Prog isa :=
  .loop (.block [.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)]) .ne

/-- The buffer's address to `rax`, the data's to `rbx`, the count to `r10`. -/
def xorArgs : List Instr :=
  [movR .rax sb, .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf))), movS .rbx c.dataSlot, movR .r10 .rcx]

/-- On past the group's blocks; ZF is set when none are left. -/
def advance : List Instr := [st c.dataSlot .rbx, .alu .sub .rdx (.reg .r10), st c.leftSlot .rdx]

/-- One group: its counter blocks, encrypted, XORed into the data. -/
def ctrGroup : Prog isa :=
  .seq (.block c.ctrBlocks) (.seq c.crypt (.seq c.groupCount (.seq (.block c.xorArgs)
    (.seq xorBlocks (.block c.advance)))))

/-- The whole function: the counter, the key, then the groups. -/
def ctr (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.ctrSetup r))
    (.seq c.prepare
      (.seq (.block [movS .rcx c.leftSlot, .alu .test .rcx (.reg .rcx)])
        (.seq (.ite .e (.block []) (.loop c.ctrGroup .ne)) (.block c.restoreRegs))))

end Core

end VG.Impl.Modes.X86_64
