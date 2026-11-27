module

public import VerifiedGarbage.Impl.AesGcm.Arm

/-! Shared descriptor-copy loop used by the ARM ChaCha20-Poly1305 gather entry. -/

@[expose] public section

namespace VG.Impl.AesGcm.Arm.SealGather

open VG.Arm

/-- `r12` at the frame (the stack pointer). The frame's words are read and
written through it. -/
def setFp : List Instr := [.addSp .r12 0]

/-- Copies the `r3` (at least 1) words at `r1` to `r2`, through `r12`. -/
def copyWords : Prog isa :=
  .loop (.block [.ldr .r12 .r1 0, .str .r12 .r2 0, addI .r1 .r1 4, addI .r2 .r2 4,
    .subs .r3 .r3 (imm 1)]) .ne

/-- The slice's address and its number of whole words. -/
def wordsArg : List Instr := [.ldr .r1 .r0 0, .ldr .r3 .r0 4, .mov .r3 (.shifted .r3 .lsr 2), .cmp .r3 (imm 0)]

/-- Its number of last bytes, the length (from the descriptor) modulo 4. -/
def bytesArg : List Instr := [.ldr .r3 .r0 4, .dp .and .r3 .r3 (imm 3), .cmp .r3 (imm 0)]

/-- Copies the slice that the descriptor at `r0` lists to `r2`, advancing
`r2` past it. -/
def copySlice : Prog isa :=
  .seq (.block wordsArg)
  (.seq (.ite .eq (.block []) copyWords)
  (.seq (.block bytesArg)
    (.ite .eq (.block []) copyLoop)))

/-- The next descriptor, and one slice fewer. -/
def next : List Instr := [addI .r0 .r0 8, .subs .lr .lr (imm 1)]

/-- Copies the `lr` (at least 1) slices that the descriptors at `r0` list to
`r2`, one after the other. -/
def gatherLoop : Prog isa := .loop (.seq copySlice (.block next)) .ne

/-- Copies the `lr` slices that the descriptors at `r0` list to `r2`. -/
def gather : Prog isa := .seq (.block [.cmp .lr (imm 0)]) (.ite .eq (.block []) gatherLoop)

end VG.Impl.AesGcm.Arm.SealGather
