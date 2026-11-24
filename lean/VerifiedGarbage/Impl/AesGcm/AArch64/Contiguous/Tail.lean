module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous.Tail
open VG.AArch64

/-- XOR both ends of a partial block. Load every source and key word before
writing the destination so a store may overlap either of the original loads. -/
def wideEnds (sz : Size) (w : Nat) : List Instr :=
  [.subImm .x .x12 .x24 w,
   .add .x .x0 .x23 .x12, .add .x .x1 .x11 .x12, .add .x .x2 .x26 .x12,
   .ldr sz .x13 .x23 0, .ldr sz .x14 .x11 0, .logic .eor sz .x13 .x13 .x14,
   .ldr sz .x14 .x0 0, .ldr sz .x15 .x1 0, .logic .eor sz .x14 .x14 .x15,
   .str sz .x13 .x26 0, .str sz .x14 .x2 0,
   .add .x .x23 .x23 .x24, .add .x .x26 .x26 .x24, imm .x24 0]

def wordTail : Prog isa :=
  .seq (.block [.lsr .x .x12 .x24 3]) <|
    .ite (.nonzero .x .x12) (.block (wideEnds .x 8)) <|
    .seq (.block [.lsr .x .x12 .x24 2]) <|
    .ite (.nonzero .x .x12) (.block (wideEnds .w 4)) DirectGather.xorBytes


def firstCall (c : Callees) : Prog isa := .ite (.zero .x .x4) (.block []) (ctrCallG c true)

def aligned (c : Callees) : Prog isa := DirectGather.alignedWith c (firstCall c) wordTail

/-- A terminal partial block has no following counter consumer. Encrypt its current
counter directly and read only the live bytes of plaintext. -/
def finalAligned (c : Callees) : Prog isa :=
  .seq (.block (crArgsG true)) <| .seq (firstCall c) <|
    .ite (.zero .x .x24) (.block []) <| .seq (Gcm.AArch64.Stitch.byRounds Tag.counter) <|
      .seq (.block [mov .x10 .x24,mov .x25 .x24,ptr .x11 .x20 64]) wordTail

end VG.Impl.AesGcm.AArch64.Contiguous.Tail
