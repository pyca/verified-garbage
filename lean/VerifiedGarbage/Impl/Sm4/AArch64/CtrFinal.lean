module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Impl.AesCtr.AArch64.Final
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Union

/-!
# SM4-CTR of a message's last piece: AArch64 implementation

`ctrFinal name whole` (schedule = x0, ctr = x1, data = x2, len = x3,
save = x4): the code of `vg_sm4_ctr_final`, around calls of an
implementation of `vg_sm4_ctr`, the function `name` with the code `whole`
(the bitsliced one, `ctrFramed`, or the one with the Armv8 SM4
instructions, `ctrFramedSm4`). Its registration frames it with a buffer of its
own on the stack, `save`, of 80 bytes, passed in `x4`:
the caller's callee-saved registers and the return address, then a block of
the code's own. It is AES-CTR's final function's
(`Impl/AesCtr/AArch64/Final.lean`) with SM4's arguments, around calls
of `vg_sm4_ctr`, framed by its own working space on the stack, as an
internal function of its own (`vg_sm4_ctr_core`, `vg_sm4_ctr_sm4_core`), which
does not zero that space: the final function as emitted zeroes the whole of
its stack on return (`Impl.Residue.AArch64.scrubAll`), as `vg_sm4_ctr` does:

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

The function as emitted zeroes `save`, the block included, on return.

Only the pointers and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64
open VG.Impl.AesCbc.AArch64 (mov)
open VG.Impl.AesCfb.AArch64 (finalSaved finalRestore)
open VG.Impl.AesCtr.AArch64 (zeroSlots tailKey)
open VG.Impl.Modes.AArch64 (xorByte)

/-- `vg_sm4_ctr`, with its working space on the stack, which it leaves to its
registration to zero. -/
def ctrFramed : Prog isa := Impl.StackScratch.AArch64.withStackScratch 3264 .x4 ctr

/-- `vg_sm4_ctr_sm4`, with its working space on the stack, which it leaves to
the function as emitted to zero. -/
def ctrFramedSm4 : Prog isa := Impl.StackScratch.AArch64.withStackScratch 224 .x4 Sm4e.ctr

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
`save`, by a call of `vg_sm4_ctr`'s implementation `name`, `whole`, and its
first `u` bytes XORed into the data. -/
def ctrFinalTail (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block ctrFinalTailArgs) (.seq (.call name whole)
    (.seq (.block tailKey) (.loop (.block (xorByte .x22 .x23)) (.nonzero .x .x23))))

/-- `vg_sm4_ctr_final`, around calls of `vg_sm4_ctr`'s implementation `name`,
`whole`. -/
def ctrFinal (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block ctrFinalSetup) (.seq (.call name whole)
    (.seq (.ite (.zero .x .x23) (.block []) (ctrFinalTail name whole)) (.block finalRestore)))

/-! ## The functions, as emitted

Each function is its code above, then its cleanup
(`Impl.Residue.AArch64.scrubAll`): the registers it writes that the calling
convention does not preserve are cleared, and the stack it uses is zeroed,
so that it returns without secret residue. `vg_sm4_ctr_final` clears the
registers its own instructions write, stated here, and those the
implementation of `vg_sm4_ctr` it calls writes. -/

namespace Fn

open VG.Impl.Residue.AArch64 (Clear scrubAll)

/-- The registers `ctrFramedSm4` writes. -/
def ctrSm4Clear : Clear :=
  ⟨[.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23],
   []⟩

/-- The registers `ctrFramed` writes. -/
def ctrClear : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- `vg_sm4_ctr_sm4`: `ctrFramedSm4`, its registers cleared and its 224 bytes
of stack zeroed. -/
def ctrSm4 : Prog isa := scrubAll 224 0 ctrSm4Clear ctrFramedSm4

/-- `vg_sm4_ctr`: `ctrFramed`, its registers cleared and its 3264 bytes of
stack zeroed. -/
def ctr : Prog isa := scrubAll 3264 0 ctrClear ctrFramed

/-- The registers `vg_sm4_ctr_final`'s own instructions write. -/
def ctrFinalOwn : Clear := ⟨[.x1, .x2, .x3, .x4, .x6, .x7, .x9, .x10, .x16, .x17], [], []⟩

/-- `vg_sm4_ctr_final` around the implementation `name`, `whole` of
`vg_sm4_ctr`, which writes the registers `cl`: `ctrFinal` with `save` in its
frame, its registers cleared and its 3344 bytes of stack zeroed. -/
def ctrFinal (cl : Clear) (name : String) (whole : Prog isa) : Prog isa :=
  scrubAll 3344 0 (ctrFinalOwn.union cl)
    (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 (Sm4.AArch64.ctrFinal name whole))

end Fn

end VG.Impl.Sm4.AArch64
