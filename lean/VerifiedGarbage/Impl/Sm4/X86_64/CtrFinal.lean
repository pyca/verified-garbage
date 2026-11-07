module

public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
public import VerifiedGarbage.Impl.AesCtr.X86_64.Final
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# SM4-CTR of a message's last piece: x86-64 implementation

`ctrFinal` (schedule = rdi, ctr = rsi, data = rdx, len = rcx, save = r8): the
code of `vg_sm4_ctr_final`, whose registration frames it with a buffer of its
own on the stack, `save`, of 64 bytes, passed in `r8`:
the caller's callee-saved registers, then a block of the code's own. It is
AES-CTR's final function's (`Impl/AesCtr/X86_64/Final.lean`) with SM4's
arguments, around calls of `vg_sm4_ctr`, framed by its own working space on
the stack (`ctrFramed`):

1. the registers saved in `save`, and the arguments kept in `rbx`
   (schedule), `r12` (ctr), `r13` (the data after its whole
   blocks), `r14` (`u = len mod 16`, the bytes after them) and `r15`
   (`save`);
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

namespace VG.Impl.Sm4.X86_64

open VG.X86_64
open VG.Impl.AesCfb.X86_64 (finalSave finalRestore)
open VG.Impl.AesCtr.X86_64 (zeroSlots tailKey)
open VG.Impl.Modes.X86_64 (xorByte)

/-- `vg_sm4_ctr`, with its working space on the stack. -/
def ctrFramed : Prog isa := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 ctr

/-- The arguments to their registers, `r13` and `r14` the data after the
whole blocks and its length, `r15` `save`, and `rcx` the number of whole
blocks. -/
def ctrFinalMoves : List Instr :=
  [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .rax),
   .mov .r14 (.reg .rcx), .alu .and .r14 (.imm 15), .mov .r13 (.reg .rcx), .alu .sub .r13 (.reg .r14),
   .alu .add .r13 (.reg .rdx), .shift .shr .rcx 4]

/-- The registers saved in `save`, at `rax`; the arguments to their
registers. -/
def ctrFinalSetup : List Instr := finalSave ++ ctrFinalMoves

/-- `save`, kept in `r15`, to `rax`. -/
def ctrFinalLoad : List Instr := [.mov .rax (.reg .r15)]

/-- The arguments of `vg_sm4_ctr` on the block after the registers:
the schedule, the counter block, the block and `n = 1`. -/
def ctrFinalTailMoves : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .rdx (.reg .rax), .alu .add .rdx (.imm 48),
   .mov32 .rcx (.imm 1)]

/-- The block, from `save` in `rax`, zeroed, and the arguments of
`vg_sm4_ctr` on it. -/
def ctrFinalTailArgs : List Instr :=
  .mov32 .r10 (.imm 0) :: (zeroSlots.map fun p => .store { base := .rax, disp := p.2 } p.1) ++ ctrFinalTailMoves

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrFinalLoad) (.seq (.block ctrFinalTailArgs) (.seq (.call "vg_sm4_ctr" ctrFramed)
    (.seq (.block ctrFinalLoad) (.seq (.block tailKey) (.loop (.block (xorByte .r13 .r14)) .ne)))))

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block [.mov .rax (.reg .r8)]) (.seq (.block ctrFinalSetup) (.seq (.call "vg_sm4_ctr" ctrFramed)
    (.seq (.block [.alu .test .r14 (.reg .r14)]) (.seq (.ite .e (.block []) ctrFinalTail)
      (.seq (.block ctrFinalLoad) (.block finalRestore))))))

end VG.Impl.Sm4.X86_64
