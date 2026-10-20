module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs

/-! # Copy accepted parameters or clear the entire output after exhausted search -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def outputArgs : List Instr :=
  bufferPointer .esi VG.Impl.Dsa.Generation.Layout.packed ++
  [.mov .edx (.mem (frameSlot 6)), .mov .ecx (.mem (frameSlot 7)), .mov .ebx (.imm (-1))]

def outputCopy : Prog isa :=
  .seq (.block outputArgs) (.seq Generate.copyMasked (.block [.mov .eax (.imm 1)]))

def outputZero : Prog isa :=
  .seq (.block [.mov .esi (.mem (frameSlot 6)), .mov .ecx (.mem (frameSlot 7)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

def finishOutput : Prog isa := .seq (.block frameSuccess) (.ite .e outputCopy outputZero)
end VG.Impl.Dsa.X86.Generation
