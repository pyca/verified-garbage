module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt

/-! # Native complete-chunk iteration for seeds and generator inputs

The comparison uses total−used before incrementing, so even tapes near the
address-width limit cannot overflow their cursor. A rejected body returns
status 3; accepted or fatal outcomes stop the loop. Running out of complete
chunks also returns 3, with a cleared loop condition.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Mgf1.X86_64

structure TapeSlots where
  base : Nat
  total : Nat
  used : Nat
  pointer : Nat

def seedTape : TapeSlots := ⟨8, 9, 10, 1⟩
def generatorTape : TapeSlots := ⟨11, 12, 20, 21⟩

def tapeReset (slots : TapeSlots) : List Instr :=
  [.mov32 .rax (.imm 0), .store (sp (8 * slots.used)) .rax]

def chunkCheck (slots : TapeSlots) (width : Nat) : List Instr :=
  [.mov .rcx (.mem (sp (8 * slots.total))), .mov .rax (.mem (sp (8 * slots.used))),
   .alu .sub .rcx (.reg .rax), .alu .cmp .rcx (.imm (BitVec.ofNat 32 width))]

def tapeTake (slots : TapeSlots) (width : Nat) : List Instr :=
  [.mov .rax (.mem (sp (8 * slots.base))), .mov .rcx (.mem (sp (8 * slots.used))),
   .alu .add .rax (.reg .rcx), .alu .add .rcx (.imm (BitVec.ofNat 32 width)),
   .store (sp (8 * slots.pointer)) .rax, .store (sp (8 * slots.used)) .rcx]

def tapeStatus : List Instr := [.mov .rax (.mem (sp 152)), .alu .cmp .rax (.imm 3)]

def tapeIteration (slots : TapeSlots) (width : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (chunkCheck slots width))
    (.ite .b
      (.block (stackStatus 3 ++ [.mov32 .rax (.imm 1), .alu .test .rax (.reg .rax)]))
      (.seq (.block (tapeTake slots width)) (.seq body (.block tapeStatus))))

def tapeLoop (slots : TapeSlots) (width : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (tapeReset slots)) (.loop (tapeIteration slots width body) .e)

end VG.Impl.Dsa.X86_64.Generation
