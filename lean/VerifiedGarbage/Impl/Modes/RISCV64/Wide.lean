module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.Wide
public import VerifiedGarbage.Impl.Words.RISCV64.Frame

/-!
# Block cipher modes on RISC-V, a group of blocks at a time

`seq2 wide narrow lg`: `seq` (`Seq.lean`) with two loops of steps. The
first takes the steps of the mode `wide`, each of `2 ^ lg` blocks
(`Mode.widen`, whose core enciphers its buffer's `2 ^ lg` blocks at once),
while at least `2 ^ lg` blocks are left; the second the steps of the mode
`narrow`, one block each, for the rest. `s3` counts the blocks left in
both: a wide step takes `2 ^ lg` from it, and the first loop goes on while
`s3 >> lg` is not zero (computed into `t0`), the second while `s3` is not
zero. Both loops branch only on `s3`, as `seq`'s does, which is public.
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

/-- One wide step: `pre`, the core, `post`, on by `step` bytes and `2 ^ lg`
blocks fewer, and whether another group is left. -/
def bodyWide (m : Mode) (lg : Nat) : Prog isa :=
  .seq (.block (c.opsCode m.pre)) (.seq c.crypt
    (.block (c.opsCode m.post ++ [.addi .s2 .s2 m.step, .addi .s3 .s3 (-((2 ^ lg : Nat) : Int)), groupsLeft lg])))

/-- The wide steps, while a group is left. -/
def loopWide (m : Mode) (lg : Nat) : Prog isa :=
  .seq (.block [groupsLeft lg]) (.ite (.zero .t0) (.block []) (.loop (c.bodyWide m lg) (.nonzero .t0)))

/-- The whole function: the wide steps, then the narrow ones. -/
def seq2 (wide narrow : Mode) (lg : Nat) : Prog isa :=
  c.seqWith (.seq (c.loopWide wide lg) (c.steps narrow)) narrow.ivOut

end Core

end VG.Impl.Modes.RISCV64
