module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame

/-! # Iterate over complete seed or generator candidates without cursor overflow

The witness cursor is independent and is never reset here. A generator
search restarts the original h tape for each accepted p candidate.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

structure TapeSlots where
  base : Nat
  total : Nat
  used : Nat
  pointer : Nat

def seedTape : TapeSlots := ⟨8, 9, 10, 1⟩
def generatorTape : TapeSlots := ⟨11, 12, 20, 21⟩

def tapeReset (slots : TapeSlots) : List Instr :=
  [.mov .eax (.imm 0), .store (frameSlot slots.used) .eax]

def chunkCheck (slots : TapeSlots) (width : Nat) : List Instr :=
  [.mov .ecx (.mem (frameSlot slots.total)), .mov .eax (.mem (frameSlot slots.used)),
   .alu .sub .ecx (.reg .eax), .alu .cmp .ecx (.imm (BitVec.ofNat 32 width))]

def tapeTake (slots : TapeSlots) (width : Nat) : List Instr :=
  [.mov .eax (.mem (frameSlot slots.base)), .mov .ecx (.mem (frameSlot slots.used)),
   .alu .add .eax (.reg .ecx), .alu .add .ecx (.imm (BitVec.ofNat 32 width)),
   .store (frameSlot slots.pointer) .eax, .store (frameSlot slots.used) .ecx]

def tapeStatus : List Instr := [.mov .eax (.mem (frameSlot 19)), .alu .cmp .eax (.imm 3)]

def tapeIteration (slots : TapeSlots) (width : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (chunkCheck slots width))
    (.ite .b (.block (frameStatus 3 ++ [.mov .eax (.imm 1), .alu .cmp .eax (.imm 0)]))
      (.seq (.block (tapeTake slots width)) (.seq body (.block tapeStatus))))

def tapeLoop (slots : TapeSlots) (width : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (tapeReset slots)) (.loop (tapeIteration slots width body) .e)
end VG.Impl.Dsa.X86.Generation
