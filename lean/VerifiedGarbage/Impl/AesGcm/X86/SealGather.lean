module

public import VerifiedGarbage.Impl.AesGcm.X86

/-! IA-32 descriptor-copy helpers shared by the ChaCha20-Poly1305 gather implementation. -/

@[expose] public section

namespace VG.Impl.AesGcm.X86.SealGather

open VG.X86

/-- `[esp + d]`. -/
def sp (d : Nat) : MemOp := at_ .esp d

/-- Copies the `ecx` (at least 1) blocks of 16 bytes at `edi` to `edx`,
through `xmm0`. -/
def copyChunks : Prog isa :=
  .loop (.block [.movdquLoad .xmm0 (at_ .edi 0), .movdquStore (at_ .edx 0) .xmm0, .alu .add .edi (imm 16),
    .alu .add .edx (imm 16), .alu .sub .ecx (imm 1)]) .ne

/-- Copies the `ecx` (at least 1) words at `edi` to `edx`, through `eax`. -/
def copyWords : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .edi 0)), .store (at_ .edx 0) .eax, .alu .add .edi (imm 4),
    .alu .add .edx (imm 4), .alu .sub .ecx (imm 1)]) .ne

/-- The slice's address and its number of whole blocks of 16 bytes. -/
def chunksArg : List Instr :=
  [.mov .edi (.mem (at_ .esi 0)), .mov .ecx (.mem (at_ .esi 4)), .shift .shr .ecx 4, .alu .cmp .ecx (imm 0)]

/-- The number of whole words of its last bytes: the length (from the
descriptor) over 4, modulo 4. -/
def wordsArg : List Instr := [.mov .ecx (.mem (at_ .esi 4)), .shift .shr .ecx 2, .alu .and .ecx (imm 3)]

/-- Its number of last bytes, the length (from the descriptor) modulo 4. -/
def bytesArg : List Instr := [.mov .ecx (.mem (at_ .esi 4)), .alu .and .ecx (imm 3)]

/-- Copies the slice that the descriptor at `esi` lists to `edx`, advancing
`edx` past it. -/
def copySlice : Prog isa :=
  .seq (.block chunksArg)
  (.seq (.ite .e (.block []) copyChunks)
  (.seq (.block wordsArg)
  (.seq (.ite .e (.block []) copyWords)
  (.seq (.block bytesArg)
    (.ite .e (.block []) copyLoop)))))

/-- The next descriptor, and one slice fewer. -/
def next : List Instr := [.alu .add .esi (imm 8), .alu .sub .ebx (imm 1)]

/-- Copies the `ebx` (at least 1) slices that the descriptors at `esi` list
to `edx`, one after the other. -/
def gatherLoop : Prog isa := .loop (.seq copySlice (.block next)) .ne

/-- Copies the `ebx` slices that the descriptors at `esi` list to `edx`. -/
def gather : Prog isa := .seq (.block [.alu .cmp .ebx (imm 0)]) (.ite .e (.block []) gatherLoop)

/-- Our caller's `ebx`, `esi` and `edi` back from the frame. -/
def restore : List Instr := [.mov .ebx (.mem (sp 36)), .mov .esi (.mem (sp 40)), .mov .edi (.mem (sp 44))]

end VG.Impl.AesGcm.X86.SealGather
