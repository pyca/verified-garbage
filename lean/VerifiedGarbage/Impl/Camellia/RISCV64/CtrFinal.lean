module

public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
public import VerifiedGarbage.Impl.AesCtr.RISCV64.Final

/-!
# Camellia-CTR of a message's last piece: RISC-V implementation

`ctrFinal` (schedule = a0, rounds = a1, ctr = a2, data = a3, len = a4,
save = a5): the code of `vg_camellia_ctr_final`, whose registration frames
it with a buffer of its own on the stack, `save`, of 80 bytes, passed in
`a5`: the return address and the caller's callee-saved registers, then a
block of the code's own. It is AES-CTR's final function's
(`Impl/AesCtr/RISCV64/Final.lean`) with Camellia's arguments, around calls
of `vg_camellia_ctr` (`Impl.Camellia.RISCV64.ctr`), which keeps its own
working space on the stack below:

1. the registers saved in `save` (AES-CFB's final functions' slots,
   `finalSaved`), and the arguments kept in `s1` (schedule), `s4` (rounds),
   `s5` (ctr), `s2` (the data after its whole blocks), `s3`
   (`u = len mod 16`, the bytes after them) and `s7` (`save`);
2. a call of `vg_camellia_ctr` on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of
   `vg_camellia_ctr` on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time;
4. the registers restored.

The registration's frame zeroes `save`, the block included, on return.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Impl.AesCfb.RISCV64 (finalSaved finalRestore)
open VG.Impl.AesCtr.RISCV64 (zeroSlots tailKey)
open VG.Impl.Modes.RISCV64 (xorStep)

/-- The registers saved in `save`, at `a5`. -/
def ctrFinalSave : List Instr := finalSaved.map fun (r, d) => .store .d r .a5 d

/-- The arguments to their registers, `s2` and `s3` the data after the
whole blocks and its length, `s7` `save`, and `a4` the number of whole
blocks. -/
def ctrFinalMoves : List Instr :=
  [mov .s1 .a0, mov .s4 .a1, mov .s5 .a2, mov .s7 .a5, .shift .srl .d .t0 .a4 4,
   .shift .sll .d .t1 .t0 4, .add .s2 .a3 .t1, .sub .s3 .a4 .t1, mov .a4 .t0]

/-- The registers saved; the arguments to their registers. -/
def ctrFinalSetup : List Instr := ctrFinalSave ++ ctrFinalMoves

/-- The arguments of `vg_camellia_ctr` on the block after the registers:
the schedule, the rounds, the counter block, the block and `n = 1`. -/
def ctrFinalTailMoves : List Instr :=
  [mov .a0 .s1, mov .a1 .s4, mov .a2 .s5, .addi .a3 .s7 64, .li .a4 1]

/-- The block, from `save` in `s7`, zeroed, and the arguments of
`vg_camellia_ctr` on it. -/
def ctrFinalTailArgs : List Instr :=
  .li .t0 0 :: (zeroSlots.map fun p => .store .d p.1 .s7 p.2) ++ ctrFinalTailMoves

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrFinalTailArgs) (.seq (.call "vg_camellia_ctr" ctr)
    (.seq (.block tailKey) (.loop (.block xorStep) (.nonzero .s3))))

/-- `vg_camellia_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block ctrFinalSetup) (.seq (.call "vg_camellia_ctr" ctr)
    (.seq (.ite (.zero .s3) (.block []) ctrFinalTail) (.block finalRestore)))

end VG.Impl.Camellia.RISCV64
