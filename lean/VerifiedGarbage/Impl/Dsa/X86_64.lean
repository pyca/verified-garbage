import VerifiedGarbage.TCB.X86_64.Isa

/-! # DSA limb arithmetic on baseline x86-64 -/
namespace VG.Impl.Dsa.X86_64
open VG.X86_64

def mulLo : Prog isa := .block [.mov .rax (.reg .rdi), .mul .rsi]
def mulHi : Prog isa := .block [.mov .rax (.reg .rdi), .mul .rsi, .mov .rax (.reg .rdx)]
def select : Prog isa := .block [
  .mov .rax (.reg .rsi), .alu .xor .rax (.reg .rdi),
  .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .rdi)]

end VG.Impl.Dsa.X86_64
