module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.AesCtr.AArch64.Final
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# SM4-CTR of a message's last piece: AArch64 implementation

`ctrFinal` (schedule = x0, ctr = x1, data = x2, len = x3, save = x4): the
code of `vg_sm4_ctr_final`, whose registration frames it with a buffer of its
own on the stack, `save`, of 80 bytes, passed in `x4`:
the caller's callee-saved registers and the return address, then a block of
the code's own. It is AES-CTR's final function's
(`Impl/AesCtr/AArch64/Final.lean`) with SM4's arguments, around calls
of `vg_sm4_ctr`, framed by its own working space on the stack
(`ctrFramed`):

1. the registers saved in `save` (AES-CFB's final functions' slots,
   `finalSaved`), and the arguments kept in `x19` (schedule), `x21` (ctr),
   `x22` (the data after its whole blocks), `x23` (`u = len mod 16`, the
   bytes after them) and `x25` (`save`);
2. a call of `vg_sm4_ctr` on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of
   `vg_sm4_ctr` on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time;
4. the registers restored.

The registration's frame zeroes `save`, the block included, on return.

Only the pointers and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64
open VG.Impl.AesCbc.AArch64 (mov)
open VG.Impl.AesCfb.AArch64 (finalSaved finalRestore)
open VG.Impl.AesCtr.AArch64 (zeroSlots tailKey)
open VG.Impl.Modes.AArch64 (xorByte)

/-- `vg_sm4_ctr`, with its working space on the stack. -/
def ctrFramed : Prog isa := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 ctr

/-- The registers saved in `save`, at `x4`. -/
def ctrFinalSave : List Instr := finalSaved.map fun (r, d) => .str .x r .x4 d

/-- The arguments to their registers, `x22` and `x23` the data after the
whole blocks and its length, `x25` `save`, and `x3` the number of whole
blocks. -/
def ctrFinalMoves : List Instr :=
  [mov .x19 .x0, mov .x21 .x1, mov .x25 .x4, .lsr .x .x9 .x3 4,
   .lsl .x .x10 .x9 4, .add .x .x22 .x2 .x10, .sub .x .x23 .x3 .x10, mov .x3 .x9]

/-- The registers saved; the arguments to their registers. -/
def ctrFinalSetup : List Instr := ctrFinalSave ++ ctrFinalMoves

/-- The arguments of `vg_sm4_ctr` on the block after the registers:
the schedule, the counter block, the block and `n = 1`. -/
def ctrFinalTailMoves : List Instr :=
  [mov .x0 .x19, mov .x1 .x21, .addImm .x .x2 .x25 64, .movz .x .x3 1 0]

/-- The block, from `save` in `x25`, zeroed, and the arguments of
`vg_sm4_ctr` on it. -/
def ctrFinalTailArgs : List Instr :=
  .movz .x .x9 0 0 :: (zeroSlots.map fun p => .str .x p.1 .x25 p.2) ++ ctrFinalTailMoves

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrFinalTailArgs) (.seq (.call "vg_sm4_ctr" ctrFramed)
    (.seq (.block tailKey) (.loop (.block (xorByte .x22 .x23)) (.nonzero .x .x23))))

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block ctrFinalSetup) (.seq (.call "vg_sm4_ctr" ctrFramed)
    (.seq (.ite (.zero .x .x23) (.block []) ctrFinalTail) (.block finalRestore)))

end VG.Impl.Sm4.AArch64
