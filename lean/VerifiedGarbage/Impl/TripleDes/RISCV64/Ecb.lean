module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Block

/-!
# Triple DES ECB on RISC-V

`dirCore d`: the block function of the direction `d` (`Block.lean`), inlined,
as a core for the modes (`Impl/Modes/RISCV64/Seq.lean`), encrypting or
decrypting the block in its buffer in place. Its slots: the buffer's one
block (slot 6), the registers the block function saves (slots 7–14), the
S-boxes' spills (slots 15–30) and a copy of the three schedules (from slot
32, byte `keyOff`), which `prepare` makes a byte at a time, since the
contracts state no alignment for the schedule and the block function reads
it a doubleword at a time. 80 slots in all, with the modes', which the mode
zeroes before it frees them.

`encrypt` and `decrypt` (schedule = a0, data = a1, n = a2) run the same
frame as the modes, with the data pointer in `s2` and the blocks left in
`s3`, and the block function on each block in place.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (copyLoop bigFrame)
open VG.Spec.TripleDes (Direction)

/-- The buffer's block. -/
def bufSlot : Nat := 6

/-- The buffer's offset in the frame. -/
def bufOff : Nat := 8 * bufSlot

/-- The schedules (at `a0`, through `t2`, which the copy advances) to their
copy in the frame. -/
def modePrepare : Prog isa :=
  .seq (.block [.addi .t0 sb keyOff, .addi .t2 .a0 0, .li .t4 384]) (copyLoop .t1 .t2 .t0 .t4)

/-- Triple DES's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Modes.RISCV64.Core where
  prepare := modePrepare
  crypt := block d sb bufOff
  total := 80
  buf := bufSlot
  G := 1
  bw := 2

namespace Ecb

open VG.Impl.Modes.RISCV64 (mov)

/-- On to the next block. -/
def advance : List Instr := [.addi .s2 .s2 8, .addi .s3 .s3 (-1)]

/-- The blocks, in the frame of the modes: the caller's `s1`–`s4` saved
(`Core.entry`, which also moves the data pointer, in `a1`, to `s2`), the
blocks left to `s3`, the schedules copied, each block encrypted or decrypted
in place, the registers restored and the frame zeroed. -/
def ecb (d : Direction) : Prog isa :=
  .ite (.zero .a2) (.block [])
    (bigFrame (dirCore d).frameBytes
      (.seq (.block (Modes.RISCV64.Core.entry ++ [mov .s3 .a2])) (.seq (dirCore d).prepare
        (.seq (.loop (.seq (block d .s2 0) (.block advance)) (.nonzero .s3))
          (.seq (.block Modes.RISCV64.Core.restore) (dirCore d).wipe)))))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end Ecb

end VG.Impl.TripleDes.RISCV64
