module
public import VerifiedGarbage.Impl.Mont.X86

/-! # Bounded p-candidate search using a separate three-word control block

Status 0 is witness exhaustion, 1 acceptance, 3 retry and 2 exhaustion of
the 4L candidate attempts. The body restores EDI to the control block.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def pSearchInit : List Instr :=
  [.mov .eax (.imm 0), .store (sc 0) .eax, .mov .eax (.imm 1), .store (sc 4) .eax]

def pSearchStatus (status : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 status)), .store (sc 8) .eax]

def pSearchAdvanceHead (limit stride : Nat) : List Instr :=
  [.mov .eax (.mem (sc 0)), .alu .add .eax (.imm 1), .store (sc 0) .eax,
   .mov .ecx (.mem (sc 4)), .alu .add .ecx (.imm (BitVec.ofNat 32 stride)), .store (sc 4) .ecx,
   .alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]

def pSearchAdvance (limit stride : Nat) : Prog isa :=
  .seq (.block (pSearchAdvanceHead limit stride))
    (.ite .b (.block (pSearchStatus 3)) (.block (pSearchStatus 2)))

def pSearchStatusCmp : List Instr := [.mov .eax (.mem (sc 8)), .alu .cmp .eax (.imm 3)]

def pSearchIteration (body : Prog isa) (limit stride : Nat) : Prog isa :=
  .seq body (.seq (.block pSearchStatusCmp)
    (.seq (.ite .e (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp)))

def pSearch (body : Prog isa) (limit stride : Nat) : Prog isa :=
  .seq (.block pSearchInit) (.loop (pSearchIteration body limit stride) .e)
end VG.Impl.Dsa.X86.Generation
