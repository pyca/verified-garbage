module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq

/-!
# CFB of a message's last piece on RISC-V, for any block cipher

`seqFinal core mode`: `seq` (`Seq.lean`) over the `len` bytes at the data,
in segments of a block, `L = 4 bw` bytes, the last of which may be shorter,
as on the other targets (`Impl/Modes/Arm/SeqFinal.lean`). The arguments are
`seq`'s, but the count, `n` in `a3` and then `s3`, is the bytes left, not
the blocks.

Each segment (`seg`) runs the mode's operations before the core, which only
copy the chaining value to the core's buffer (`cfbEnc`'s and `cfbDec`'s:
neither reads the data before the core, so that a partial segment reads
only its bytes), and the core, giving `Oⱼ` in the buffer. Then `t0 := L`,
and if `s3 < L` (`bltu`), fewer than a block's bytes are left (`tail`):
`Oⱼ` goes to the chaining value, the block to continue from, which goes
back to the IV at the end as after a whole block, and its first `s3` bytes
are XORed into the data a byte at a time (`xorStep`, through `t0` and `t1`,
the buffer's bytes at `t2`), which leaves `s3` zero. Otherwise the mode's
operations after the core, and on by `L` bytes (`advanceBytes`). The core is
inlined once, in the segment.

As in `seq`, only the pointers and `len` can affect timing: the branches are
on `s3` (and the data's address, for `aligned`) alone.
-/

@[expose] public section

namespace VG.Impl.Modes.RISCV64

open VG.RISCV64
open VG.Impl.Modes

/-- The data's byte at `s2` XORed with the buffer's at `t2`, through `t0`
and `t1`; both on to the next byte, and one fewer left in `s3`. -/
def xorStep : List Instr :=
  [.load .b .t0 .s2 0, .load .b .t1 .t2 0, .logic .xor .t0 .t0 .t1, .store .b .t0 .s2 0,
   .addi .s2 .s2 1, .addi .t2 .t2 1, .addi .s3 .s3 (-1)]

namespace Core

variable (c : Core)

/-- A block's bytes. -/
def L : Nat := 4 * c.bw

/-- A partial segment: the buffer's block to the chaining value, and its
first bytes XORed into the bytes left, none left after them. -/
def tail : Prog isa :=
  .seq (.block (c.opsCode false (copyBlk c.bw .chn .buf) ++ [.addi .t2 sb ((8 * c.buf : Nat) : Int)]))
    (.loop (.block xorStep) (.nonzero .s3))

/-- On by a block, a block's bytes fewer left. -/
def advanceBytes : List Instr := [.addi .s2 .s2 c.L, .addi .s3 .s3 (-(c.L : Int))]

/-- One segment: `pre`, the core, then a partial segment if fewer than a
block's bytes are left, else `post` and on by a block. -/
def seg (w : Bool) (m : Mode) : Prog isa :=
  .seq (.block (c.opsCode w m.pre)) (.seq c.crypt (.seq (.block [.li .t0 c.L])
    (.ite (.ltu .s3 .t0) c.tail (.block (c.opsCode w m.post ++ c.advanceBytes)))))

/-- The segments, while any bytes are left. -/
def segs (w : Bool) (m : Mode) : Prog isa := .ite (.zero .s3) (.block []) (.loop (c.seg w m) (.nonzero .s3))

/-- The whole function: `seq`'s, over segments, the chaining value back to
the IV. -/
def seqFinal (m : Mode) : Prog isa := c.seqWith (aligned m.step fun w => c.segs w m) true

end Core

end VG.Impl.Modes.RISCV64
