module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.AesCfb.Arm.Final

/-!
# SM4-CTR of a message's last piece: 32-bit ARM implementation

`ctrFinal` (schedule = r0, ctr = r1, data = r2, len = r3, save = `[sp]`):
the code of `vg_sm4_ctr_final`, whose registration frames it with a buffer of
its own on the stack, `save`, the fifth argument, of 56 bytes: the caller's
callee-saved registers and its return address, then, at 40, a block of the
code's own. It is AES-CTR's final function's
(`Impl/AesCtr/Arm/Final.lean`) with SM4's arguments, around calls of
`vg_sm4_ctr`, framed by its own working space on the stack (`ctrFramed`),
whose arguments are all in registers:

1. the registers saved in `save` (through `r12`), and the arguments kept in
   `r4` (schedule), `r6` (ctr), `r7` (the data after its whole blocks) and
   `r8` (`u = len mod 16`, the bytes after them), and `r3` the number of
   whole blocks;
2. a call of `vg_sm4_ctr` on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block at `save + 40` zeroed, a call of `vg_sm4_ctr` on
   that one block, which leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and
   the first `u` bytes of the block XORed into the `u` bytes left, a byte at
   a time (the modes' `xorByte`);
4. the registers restored from `save`, whose address is reloaded from the
   stack.

The registration's frame zeroes `save`, the block included, on return.
Only the pointers and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesCfb.Arm (finalSave finalRestore)
open VG.Impl.Modes.Arm (xorByte)

/-- `vg_sm4_ctr`, with its working space on the stack. -/
def ctrFramed : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 BatchCtr.ctr

/-- `save`, the stack argument, to `r12`. -/
def ctrSave : List Instr := [.ldrSp .r12 0]

/-- The arguments to their registers: `r4` the schedule, `r6` the counter
block, `r8` the bytes after the whole blocks, `r3` their number and `r7` the
data after them. -/
def ctrFinalMoves : List Instr :=
  [mov .r4 .r0, mov .r6 .r1, .dp .and .r8 .r3 (.imm 15), .mov .r3 (.shifted .r3 .lsr 4),
   .dp .add .r7 .r2 (.shifted .r3 .lsl 4)]

/-- The registers saved; the arguments to their registers. -/
def ctrFinalSetup : List Instr := ctrSave ++ finalSave ++ ctrFinalMoves

/-- The call of `vg_sm4_ctr`. -/
def ctrCall : Prog isa := .call "vg_sm4_ctr" ctrFramed

/-- The block at `save + 40` zeroed, through `r0`, and the arguments of
`vg_sm4_ctr` on it: the schedule, the counter block, the block and `n = 1`. -/
def ctrTailArgs : List Instr :=
  ctrSave ++ [.mov .r0 (.imm 0), .str .r0 .r12 40, .str .r0 .r12 44, .str .r0 .r12 48, .str .r0 .r12 52,
    mov .r0 .r4, mov .r1 .r6, .dp .add .r2 .r12 (.imm 40), .mov .r3 (.imm 1)]

/-- The arguments of the XOR: the block (`r0`), the data after the whole
blocks (`r6`) and the bytes left (`r7`). -/
def ctrXorArgs : List Instr := ctrSave ++ [.dp .add .r0 .r12 (.imm 40), mov .r6 .r7, mov .r7 .r8]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrTailArgs) (.seq ctrCall (.seq (.block ctrXorArgs) (.loop (.block xorByte) .ne)))

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block ctrFinalSetup) (.seq ctrCall
    (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) ctrFinalTail) (.block (ctrSave ++ finalRestore)))))

end VG.Impl.Sm4.Arm
