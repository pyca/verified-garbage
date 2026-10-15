module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init

/-! # Native private-key rejection budgets -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Generation

open VG VG.X86_64

def keyInitializeState : Prog isa := .block [
  .mov32 .rax (.imm 128), .store (field 0) .rax, .store (field 1) .rax,
  .store (field 2) .rsi, .store (field 3) .rsi, .mov32 .rax (.imm 1)]

def keyInit : Prog isa := .seq (.block [.alu .cmp .rsi (.imm 64)])
  (.ite .b clear (.seq (.block [.alu .cmp .rsi (.imm 1025)])
    (.ite .ae clear keyInitializeState)))

end VG.Impl.Ffdh.X86_64.Generation
