module

public import VerifiedGarbage.TCB.X86_64.Isa

@[expose] public section

namespace VG.Impl.Ffdh.X86_64
open VG.X86_64

/-- No memory, branches or operand-dependent instructions. -/
def choose : Prog isa := .block [
  .mov .rax (.reg .rdi),
  .alu .xor .rax (.reg .rsi),
  .alu .and .rdx (.imm 1),
  .mov .rcx (.imm 0),
  .alu .sub .rcx (.reg .rdx),
  .alu .and .rax (.reg .rcx),
  .alu .xor .rax (.reg .rdi)]
end VG.Impl.Ffdh.X86_64
