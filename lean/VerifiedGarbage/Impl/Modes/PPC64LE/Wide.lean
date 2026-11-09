module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.Wide

/-!
# Block cipher modes on PPC64LE, a group of blocks at a time

`seq2 wide narrow lg`: `seq` (`Seq.lean`) with two loops of steps, as on
RISC-V (`Impl/Modes/RISCV64/Wide.lean`). The first takes the steps of the
mode `wide`, each of `2 ^ lg` blocks (`Mode.widen`, whose core enciphers
its buffer's `2 ^ lg` blocks at once), while at least `2 ^ lg` blocks are
left; the second the steps of the mode `narrow`, one block each, for the
rest. `r30` counts the blocks left in both: a wide step takes `2 ^ lg`
from it, and the first loop goes on while `r30 >> lg` is not zero
(computed into `r8`, which the operations use as scratch), the second
while `r30` is not zero. Both loops branch only on `r30`, as `seq`'s does,
which is public.

`seq2With one wide narrow lg`: `seq2`, with the narrow steps on the core
`c.withOne one` (`c` with `one` as its code, which enciphers only the
buffer's first block), for a core whose code costs as much on one block as
on its `G`.

`seqLevelsWith one wide lgs narrow`: `seq2With` with a wide loop for each
`lg` of `lgs` in turn, of the mode `wide (2 ^ lg)` (`levels`), before the
narrow steps: each takes the groups of `2 ^ lg` of the blocks the ones
before it left, all on the same core (`2 ^ lg ≤ G`), so that fewer blocks
than the core's `G` still take one call of its code a group rather than
one a block. `seq2With` is the case of one level.
-/

@[expose] public section

namespace VG.Impl.Modes.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes

namespace Core

variable (c : Core)

/-- `r8 := r30 >> lg`: whether a group of `2 ^ lg` blocks is left. -/
def groupsLeft (lg : Nat) : Instr := .lsr .d .r8 .r30 lg

/-- One wide step: `pre`, the core, `post`, on by `step` bytes and `2 ^ lg`
blocks fewer, and whether another group is left. -/
def bodyWide (m : Mode) (lg : Nat) : Prog isa :=
  .seq (.block (c.opsCode m.pre)) (.seq c.crypt
    (.block (c.opsCode m.post ++ [.addi .r31 .r31 m.step, .subi .r30 .r30 (2 ^ lg), groupsLeft lg])))

/-- The wide steps, while a group is left. -/
def loopWide (m : Mode) (lg : Nat) : Prog isa :=
  .seq (.block [groupsLeft lg]) (.ite (.zero .d .r8) (.block []) (.loop (c.bodyWide m lg) (.nonzero .d .r8)))

/-- The whole function: the wide steps, then the narrow ones. -/
def seq2 (wide narrow : Mode) (lg : Nat) : Prog isa :=
  c.seqWith (.seq (c.loopWide wide lg) (c.steps narrow)) narrow.ivOut

/-- The core `c` with the code `one` on the first block of its buffer. -/
def withOne (one : Prog isa) : Core := { c with crypt := one, G := 1 }

/-- `seq2`, with the narrow steps on `c.withOne one`. -/
def seq2With (one : Prog isa) (wide narrow : Mode) (lg : Nat) : Prog isa :=
  c.seqWith (.seq (c.loopWide wide lg) ((c.withOne one).steps narrow)) narrow.ivOut

/-- The wide loops of the modes `wide (2 ^ lg)` for each `lg` of `lgs` in
turn, then `rest`. -/
def levels (wide : Nat → Mode) : List Nat → Prog isa → Prog isa
  | [], rest => rest
  | lg :: lgs, rest => .seq (c.loopWide (wide (2 ^ lg)) lg) (levels wide lgs rest)

/-- `seq2With`, with a wide loop for each of `lgs`. -/
def seqLevelsWith (one : Prog isa) (wide : Nat → Mode) (lgs : List Nat) (narrow : Mode) : Prog isa :=
  c.seqWith (c.levels wide lgs ((c.withOne one).steps narrow)) narrow.ivOut

end Core

end VG.Impl.Modes.PPC64LE
