module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init

/-! # Native FFDH key generation: validation and rejection budgets -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Impl.Ffdh.X86_64.Generation

/-- Both budgets 128, the width and the first request `p_len`. -/
def initializeState : Prog isa := .block [
  .mov32 .rax (.imm 128), .store (field 0) .rax, .store (field 1) .rax,
  .store (field 2) .rsi, .store (field 3) .rsi, .mov32 .rax (.imm 1)]

def init : Prog isa := .seq (.block [.alu .cmp .rsi (.imm 64)])
  (.ite .b clear (.seq (.block [.alu .cmp .rsi (.imm 1025)])
    (.ite .ae clear initializeState)))

end VG.Impl.Ffdh.X86_64.KeyGeneration
