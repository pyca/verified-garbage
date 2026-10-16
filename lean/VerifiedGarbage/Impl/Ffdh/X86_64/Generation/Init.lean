module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Native validation and limits for FFDH parameter generation -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Generation

open VG VG.X86_64

def field (j : Nat) : MemOp := { base := .rdi, disp := (8 * j : Nat) }

def clear : Prog isa := .block [
  .mov32 .rax (.imm 0), .store (field 0) .rax, .store (field 1) .rax,
  .store (field 2) .rax, .store (field 3) .rax]

def initializeState : Prog isa := .block [
  .mov .rax (.reg .rsi), .mul .rsi, .shift .shl .rax 6, .store (field 0) .rax,
  .mov .rcx (.reg .rsi), .alu .add .rcx (.imm 7), .shift .shr .rcx 3,
  .store (field 1) .rcx, .mov .rax (.reg .rcx), .shift .shl .rax 15,
  .alu .add .rax (.reg .rcx), .store (field 2) .rax,
  .shift .shl .rcx 9, .store (field 3) .rcx, .mov32 .rax (.imm 1)]

def checkGenerator : Prog isa := .seq (.block [.alu32 .cmp .rdx (.imm 2)])
  (.ite .e initializeState (.seq (.block [.alu32 .cmp .rdx (.imm 5)]) (.ite .e initializeState clear)))

def checks : Prog isa := .seq (.block [.alu .cmp .rsi (.imm 512)])
  (.ite .b clear (.seq (.block [.alu .cmp .rsi (.imm 8193)]) (.ite .ae clear checkGenerator)))

def init : Prog isa := .seq (.block [.mov32 .rdx (.reg .rdx)]) checks

end VG.Impl.Ffdh.X86_64.Generation
