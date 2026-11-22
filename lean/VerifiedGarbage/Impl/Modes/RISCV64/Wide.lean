module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.Wide
public import VerifiedGarbage.Impl.Words.RISCV64.Frame

/-!
# Block cipher modes on RISC-V, a group of blocks at a time

`seq2 narrow lg`: `seq` (`Seq.lean`) with two loops of steps. The
first takes the steps of the mode `narrow` widened to groups of `2 ^ lg`
blocks (`Mode.widen`, whose core enciphers its buffer's `2 ^ lg` blocks at
once), while at least `2 ^ lg` blocks are left; the second the steps of
`narrow`, one block each, for the rest. A wide step runs `narrow`'s `pre`
on each block of its group in a loop (`groupLoop`), with the block of the
data at `t4` and the block of the buffer at `t3` (`gloc`), counted by `t5`:
the same operations, in the same order, as the widened mode's `pre`, at a
loop's cost rather than a copy for each block. Then the core, then `post`
the same way. `s3` counts the blocks left in both loops of steps: a wide
step takes `2 ^ lg` from it, and the first loop goes on while `s3 >> lg` is
not zero (computed into `t0`), the second while `s3` is not zero. Both
loops branch only on `s3`, as `seq`'s does, which is public, and the
groups' loops on `t5`, which counts a public number.

`seqLevels lgs narrow`: `seq2` with a wide loop for each `lg` of `lgs`
in turn, of `narrow` widened to `2 ^ lg` blocks (`levels`), before the
narrow steps: each takes the groups of `2 ^ lg` of the blocks the ones
before it left, all on the same core (`2 ^ lg ≤ G`). A core whose code
costs as much on one block as on its `G` then takes one call of its code
for each power of two in the number of blocks a message leaves after its
groups of `G`, rather than one a block. `seq2` is the case of one level.

`seqLevelsWith one lgs narrow`: `seqLevels`, with the narrow steps on
the core `c.withOne one` (`c` with `one` as its code, which enciphers only
the buffer's first block), for a core whose code costs more on one block
than code of its own for one would.
-/

@[expose] public section

namespace VG.Impl.Modes.RISCV64

open VG.RISCV64
open VG.Impl.Modes
open VG.Impl.Words.RISCV64 (bigFrame)

namespace Core

variable (c : Core)

/-- `t0 := s3 >> lg`: whether a group of `2 ^ lg` blocks is left. -/
def groupsLeft (lg : Nat) : Instr := .shift .srl .d .t0 .s3 lg

/-- The areas of a group's block in its loops: the data's block at `t4`,
the buffer's at `t3`; the chaining value where it is. -/
def gloc : Loc → Reg × Nat
  | .dat => (.t4, 0)
  | .chn => (sb, 8 * chnSlot)
  | .buf => (.t3, 0)

/-- The operations `os` of a block on each of the `g` blocks of a group:
`t3` and `t4` at the block of the buffer (of `4 bw` bytes) and of the data
(of `st`), `t5` the blocks left. -/
def groupLoop (w : Bool) (os : List Op) (st g : Nat) : Prog isa :=
  .seq (.block [.addi .t3 sb ((8 * c.buf : Nat) : Int), mov .t4 .s2, .li .t5 (g : Int)])
    (.loop (.block (opsCodeAt gloc w os ++
      [.addi .t3 .t3 ((4 * c.bw : Nat) : Int), .addi .t4 .t4 (st : Int), .addi .t5 .t5 (-1)])) (.nonzero .t5))

/-- One wide step of `2 ^ lg` blocks of the mode `m`: `m.pre` on each, the
core, `m.post` on each, on by `2 ^ lg` steps, and whether another group is
left. -/
def bodyWide (w : Bool) (m : Mode) (lg : Nat) : Prog isa :=
  .seq (c.groupLoop w m.pre m.step (2 ^ lg)) (.seq c.crypt (.seq (c.groupLoop w m.post m.step (2 ^ lg))
    (.block [.addi .s2 .s2 ((2 ^ lg * m.step : Nat) : Int), .addi .s3 .s3 (-((2 ^ lg : Nat) : Int)), groupsLeft lg])))

/-- The wide steps, while a group is left. -/
def loopWide (w : Bool) (m : Mode) (lg : Nat) : Prog isa :=
  .seq (.block [groupsLeft lg]) (.ite (.zero .t0) (.block []) (.loop (c.bodyWide w m lg) (.nonzero .t0)))

/-- The whole function: the wide steps, then the narrow ones. -/
def seq2 (narrow : Mode) (lg : Nat) : Prog isa :=
  c.seqWith (aligned narrow.step fun w => .seq (c.loopWide w narrow lg) (c.steps w narrow)) narrow.ivOut

/-- The wide loops of the mode `m` on `2 ^ lg` blocks for each `lg` of `lgs`
in turn, then `rest`. -/
def levels (w : Bool) (m : Mode) : List Nat → Prog isa → Prog isa
  | [], rest => rest
  | lg :: lgs, rest => .seq (c.loopWide w m lg) (levels w m lgs rest)

/-- `seq2`, with a wide loop for each of `lgs`. -/
def seqLevels (lgs : List Nat) (narrow : Mode) : Prog isa :=
  c.seqWith (aligned narrow.step fun w => c.levels w narrow lgs (c.steps w narrow)) narrow.ivOut

/-- The core `c` with the code `one` on the first block of its buffer. -/
def withOne (one : Prog isa) : Core := { c with crypt := one, G := 1 }

/-- `seqLevels`, with the narrow steps on `c.withOne one`. -/
def seqLevelsWith (one : Prog isa) (lgs : List Nat) (narrow : Mode) : Prog isa :=
  c.seqWith (aligned narrow.step fun w => c.levels w narrow lgs ((c.withOne one).steps w narrow)) narrow.ivOut

end Core

end VG.Impl.Modes.RISCV64
