module

public import VerifiedGarbage.Impl.Camellia.Arm.Ctr
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.AesCfb.Arm.Final

/-!
# Camellia-CTR of a message's last piece: 32-bit ARM implementation

`ctrFinal` (schedule = r0, rounds = r1, ctr = r2, data = r3, len = `[sp]`,
save = `[sp + 4]`): the code of `vg_camellia_ctr_final`, whose registration
frames it with a buffer of its own on the stack, `save`, the sixth argument,
of 56 bytes: the caller's callee-saved registers and its return address,
then, at 40, a block of the code's own. It is AES-CTR's final function's
(`Impl/AesCtr/Arm/Final.lean`) with Camellia's arguments, around calls of
`vg_camellia_ctr`, framed by its own working space on the stack
(`ctrFramed`), in a frame that pushes its stack argument, the number of
blocks (`push {r12, lr}`):

1. the registers saved in `save` (through `r12`), and the arguments kept in
   `r4` (schedule), `r5` (rounds), `r6` (ctr), `r7` (the data after its
   whole blocks) and `r8` (`u = len mod 16`, the bytes after them), and
   `r12` the number of whole blocks;
2. a call of `vg_camellia_ctr` on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block at `save + 40` zeroed, a call of `vg_camellia_ctr`
   on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`,
   and the first `u` bytes of the block XORed into the `u` bytes left, a byte
   at a time (the modes' `xorByte`);
4. the registers restored from `save`, whose address is reloaded from the
   stack.

The registration's frame zeroes `save`, the block included, on return.
Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesCfb.Arm (finalSave finalRestore)
open VG.Impl.Modes.Arm (xorByte)

/-- `vg_camellia_ctr`, with its working space on the stack. -/
def ctrFramed : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 ctr

/-- `save`, the second stack argument, to `r12`. -/
def ctrSave : List Instr := [.ldrSp .r12 4]

/-- The arguments to their registers: `r4` the schedule, `r5` the rounds,
`r6` the counter block, `r8` the bytes after the whole blocks, `r12` their
number and `r7` the data after them. -/
def ctrFinalMoves : List Instr :=
  [mov .r4 .r0, mov .r5 .r1, mov .r6 .r2, .ldrSp .r8 0, .mov .r12 (.shifted .r8 .lsr 4),
   .dp .and .r8 .r8 (.imm 15), .dp .add .r7 .r3 (.shifted .r12 .lsl 4)]

/-- The registers saved; the arguments to their registers. -/
def ctrFinalSetup : List Instr := ctrSave ++ finalSave ++ ctrFinalMoves

/-- The call of `vg_camellia_ctr`, with the number of blocks in `r12`
pushed as its stack argument. -/
def ctrCall : Prog isa := .frame (.push [.r12, .lr]) (.call "vg_camellia_ctr" ctrFramed) (.pop .r12 8)

/-- The block at `save + 40` zeroed, through `r0`, and the arguments of
`vg_camellia_ctr` on it: the schedule, the rounds, the counter block, the
block and, in `r12`, `n = 1`. -/
def ctrTailArgs : List Instr :=
  ctrSave ++ [.mov .r0 (.imm 0), .str .r0 .r12 40, .str .r0 .r12 44, .str .r0 .r12 48, .str .r0 .r12 52,
    mov .r0 .r4, mov .r1 .r5, mov .r2 .r6, .dp .add .r3 .r12 (.imm 40), .mov .r12 (.imm 1)]

/-- The arguments of the XOR: the block (`r0`), the data after the whole
blocks (`r6`) and the bytes left (`r7`). -/
def ctrXorArgs : List Instr := ctrSave ++ [.dp .add .r0 .r12 (.imm 40), mov .r6 .r7, mov .r7 .r8]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrTailArgs) (.seq ctrCall (.seq (.block ctrXorArgs) (.loop (.block xorByte) .ne)))

/-- `vg_camellia_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block ctrFinalSetup) (.seq ctrCall
    (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) ctrFinalTail) (.block (ctrSave ++ finalRestore)))))

end VG.Impl.Camellia.Arm
