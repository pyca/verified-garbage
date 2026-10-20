module
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Mont.X86

/-! # Persistent 32-bit parameter-search frame

Slot numbers mirror the x86-64 search model. The frame holds pointers,
public widths and tape cursors; arithmetic and hashing use separate scratch
areas. Callees use stack space below this frame.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def frameBytes : Nat := 148
def frameSlot (i : Nat) : MemOp := at_ .esp (4 * i)

def frameStatus (status : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 status)), .store (frameSlot 19) .eax]

def frameSuccess : List Instr := [.mov .eax (.mem (frameSlot 19)), .alu .cmp .eax (.imm 1)]

def onSuccess (next : Prog isa) : Prog isa :=
  .seq (.block frameSuccess) (.ite .e next (.block []))

def workspaceBase : List Instr :=
  [.mov .edi (.mem (frameSlot 5)),
   .alu .add .edi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic))]

def controlBase : List Instr :=
  [.mov .edi (.mem (frameSlot 5)),
   .alu .add .edi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.control))]

end VG.Impl.Dsa.X86.Generation
