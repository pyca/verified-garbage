module

public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops

/-!
# Gathering a list of slices: RISC-V

`gather` copies the `a5` slices that the descriptors at `a4` list (each an
address and a length, 16 bytes), one after the other, to `a6`, as the
functions encrypting out of place from a list of slices do before encrypting
in place (`seal_gather`). Loads and stores fault unless naturally aligned,
and the contracts state no alignment for the descriptors or the slices, so
the descriptors are read a word at a time and the slices copied a byte at a
time: with `t0` the slice's address and `t1` its length, `copyLoop` copies
it through `t2`, advancing `a6` past it. It writes only `t0`–`t4` and
`a4`–`a6`, all caller-saved, and its branches are on the number of slices
and their lengths alone.
-/

@[expose] public section

namespace VG.Impl.Gather.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadLE64 copyLoop)

/-- The next descriptor: the slice's address in `t0` and length in `t1`. -/
def next : List Instr :=
  loadLE64 .t0 .t3 .t4 .a4 0 ++ loadLE64 .t1 .t3 .t4 .a4 8 ++ ([.addi .a4 .a4 16] : List Instr)

/-- Copies the `t1` bytes at `t0` to `a6`, advancing `a6` past them. -/
def copySlice : Prog isa := .ite (.zero .t1) (.block []) (copyLoop .t2 .t0 .a6 .t1)

/-- Copies the `a5` (at least 1) slices that the descriptors at `a4` list to
`a6`, one after the other. -/
def gatherLoop : Prog isa :=
  .loop (.seq (.block next) (.seq copySlice (.block [.addi .a5 .a5 (-1)]))) (.nonzero .a5)

/-- Copies the `a5` slices that the descriptors at `a4` list to `a6`. -/
def gather : Prog isa := .ite (.zero .a5) (.block []) gatherLoop

end VG.Impl.Gather.RISCV64
