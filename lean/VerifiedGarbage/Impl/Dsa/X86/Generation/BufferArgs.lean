module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame

/-! # Address persistent buffers from the caller's saved scratch pointer -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def bufferPointer (reg : Reg) (offset : Nat) : List Instr :=
  [.mov reg (.mem (frameSlot 5)), .alu .add reg (.imm (BitVec.ofNat 32 offset))]

def qHashArgs : List Instr :=
  [.mov .esi (.mem (frameSlot 1))] ++ bufferPointer .edi VG.Impl.Dsa.Generation.Layout.q ++
    [.mov .ebp (.mem (frameSlot 14))]

def candidatePointer (offset : Nat) : List Instr :=
  bufferPointer .eax offset ++ [.store (frameSlot 22) .eax]
end VG.Impl.Dsa.X86.Generation
