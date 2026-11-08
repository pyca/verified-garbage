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

end Core

end VG.Impl.Modes.PPC64LE
