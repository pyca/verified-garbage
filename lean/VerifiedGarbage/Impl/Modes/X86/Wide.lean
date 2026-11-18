module

public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.Wide

/-!
# Block cipher modes on x86 (32-bit), a group of blocks at a time

`seqLevels wide gs narrow`: `seq` (`Seq.lean`) with a loop of steps for each
group size `g` of `gs` in turn, then the steps of the mode `narrow`, one
block each, for the rest, as on RISC-V (`Impl/Modes/RISCV64/Wide.lean`). The
loop for `g` takes the steps of the mode `wide g`, each of `g` blocks
(`Mode.widen`, whose core enciphers its buffer's first `g` blocks at
once, `g ≤ G`), while at least `g` blocks are left: each level takes the
groups of the blocks the ones before it left, all on the same core. A core
whose code costs as much on one block as on its `G` then takes one run of
its code for each group, of sizes `gs`, that the number of blocks is the
sum of, rather than one a block.

The blocks left are counted in the slot `nSlot`, as in `seq`: a wide step
takes `g` from it, and its loop goes on while it is at least `g` (`cmp`,
and CF clear), the narrow one while it is not zero. Every loop branches
only on that count, which is public; it is compared again from its slot
before each loop (`leftCmp`, `leftTest`), where the stores of the step
before have left it (`advanceWide`, `advance`).
-/

@[expose] public section

namespace VG.Impl.Modes.X86

open VG.X86
open VG.Impl.Modes

namespace Core

variable (c : Core)

/-- The blocks left, compared with `g`: CF is set if fewer are left. -/
def leftCmp (g : Nat) : List Instr :=
  [.mov .eax (.mem (slotAt c.nSlot)), .alu .cmp .eax (.imm (BitVec.ofNat 32 g))]

/-- Whether no block is left (ZF). -/
def leftTest : List Instr := [.mov .eax (.mem (slotAt c.nSlot)), .alu .test .eax (.reg .eax)]

/-- On by `step` bytes, `g` blocks fewer, both stored back, and whether
another group is left (CF set if not). -/
def advanceWide (step g : Nat) : List Instr :=
  [.alu .add .esi (.imm (BitVec.ofNat 32 step)), .alu .sub .ebp (.imm (BitVec.ofNat 32 g)),
   .store (slotAt c.dSlot) .esi, .store (slotAt c.nSlot) .ebp, .alu .cmp .ebp (.imm (BitVec.ofNat 32 g))]

/-- One wide step: `pre`, the core, `post`, and on by a group. -/
def bodyWide (m : Mode) (g : Nat) : Prog isa :=
  .seq (.block (c.load ++ c.opsCode m.pre)) (.seq c.crypt
    (.block (c.load ++ c.opsCode m.post ++ c.advanceWide m.step g)))

/-- The wide steps, while a group of `g` blocks is left. -/
def loopWide (m : Mode) (g : Nat) : Prog isa :=
  .seq (.block (c.leftCmp g)) (.ite .b (.block []) (.loop (c.bodyWide m g) .ae))

/-- The steps of `m`, one block each, while a block is left. -/
def steps (m : Mode) : Prog isa :=
  .seq (.block c.leftTest) (.ite .e (.block []) (.loop (c.body m) .ne))

/-- The wide loops of the modes `wide g` for each `g` of `gs` in turn, then
`rest`. -/
def levels (wide : Nat → Mode) : List Nat → Prog isa → Prog isa
  | [], rest => rest
  | g :: gs, rest => .seq (c.loopWide (wide g) g) (levels wide gs rest)

/-- `seq`, with `loops` for its loop of steps. -/
def seqWith (loops : Prog isa) (ivOut : Bool) : Prog isa :=
  .seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare (.seq (.block c.args)
    (.seq loops (.block ((if ivOut then c.ivBack else []) ++ c.restore)))))

/-- The whole function: a wide loop for each of `gs`, then the narrow
steps. -/
def seqLevels (wide : Nat → Mode) (gs : List Nat) (narrow : Mode) : Prog isa :=
  c.seqWith (c.levels wide gs (c.steps narrow)) narrow.ivOut

end Core

end VG.Impl.Modes.X86
