module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr
public import VerifiedGarbage.Impl.AesCtr.PPC64LE.Final
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# SM4-CTR of a message's last piece: PPC64LE implementation

`ctrFinal` (schedule = r3, ctr = r4, data = r5, len = r6, save = r7): the
code of `vg_sm4_ctr_final`, whose registration frames it with a buffer of its
own on the stack, `save`, of 80 bytes, passed in `r7`: the return address and
the caller's callee-saved registers, then a block of the code's own. It is
AES-CTR's final function's (`Impl/AesCtr/PPC64LE/Final.lean`) with SM4's
arguments, around calls of `vg_sm4_ctr`, framed by its own working space on
the stack (`ctrFramed`):

1. the return address (through `r0`) and the registers saved in `save`
   (AES-CFB's final functions' slots, `finalSaved`), and the arguments kept
   in `r14` (schedule), `r16` (ctr), `r31` (the data after its whole
   blocks), `r30` (`u = len mod 16`, the bytes after them) and `r20`
   (`save`);
2. a call of `vg_sm4_ctr` on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of
   `vg_sm4_ctr` on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time;
4. the registers and the return address restored.

The registration's frame zeroes `save`, the block included, on return.

Only the pointers and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.AesCfb.PPC64LE (finalSaved finalRestore)
open VG.Impl.AesCtr.PPC64LE (zeroSlots tailKey)
open VG.Impl.Modes.PPC64LE (tailByte)

/-- `vg_sm4_ctr`, with its working space on the stack. -/
def ctrFramed : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 ctr

/-- A call of `vg_sm4_ctr`. -/
def ctrCall : Prog isa := .call "vg_sm4_ctr" ctrFramed

/-- The return address and the registers saved in `save`, at `r7`. -/
def ctrFinalSave : List Instr := .mflr .r0 :: finalSaved.map fun (r, d) => .store .d r .r7 d

/-- The arguments to their registers, `r31` and `r30` the data after the
whole blocks and its length, `r20` `save`, and `r6` the number of whole
blocks. -/
def ctrFinalMoves : List Instr :=
  [mov .r14 .r3, mov .r16 .r4, mov .r20 .r7, .lsr .d .r10 .r6 4,
   .lsl .r11 .r10 4, .add .r31 .r5 .r11, .sub .r30 .r6 .r11, mov .r6 .r10]

/-- The registers saved; the arguments to their registers. -/
def ctrFinalSetup : List Instr := ctrFinalSave ++ ctrFinalMoves

/-- The arguments of `vg_sm4_ctr` on the block after the registers: the
schedule, the counter block, the block and `n = 1`. -/
def ctrFinalTailMoves : List Instr :=
  [mov .r3 .r14, mov .r4 .r16, .addi .r5 .r20 64, .li .r6 1]

/-- The block, from `save` in `r20`, zeroed, and the arguments of
`vg_sm4_ctr` on it. -/
def ctrFinalTailArgs : List Instr :=
  .li .r9 0 :: (zeroSlots.map fun p => .store .d p.1 .r20 p.2) ++ ctrFinalTailMoves

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrFinalTailArgs) (.seq ctrCall
    (.seq (.block tailKey) (.loop (.block tailByte) (.nonzero .d .r30))))

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block ctrFinalSetup) (.seq ctrCall
    (.seq (.ite (.zero .d .r30) (.block []) ctrFinalTail) (.block finalRestore)))

end VG.Impl.Sm4.PPC64LE
