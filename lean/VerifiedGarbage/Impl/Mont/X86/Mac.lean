module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Shared multiply-accumulate word for x86 Montgomery arithmetic -/

@[expose] public section
namespace VG.Impl.Mont.X86
open VG VG.X86

/-- Add `[edi + mult] * [ecx + input]` and the carry `ebx` to
`[ebp + output]`, returning the next carry in `ebx`. Both the fixed-width
and runtime-width loops use this instruction sequence. -/
def macWord (output input mult : Nat) : List Instr :=
  [.mov .eax (.mem (sc mult)), .mov .edx (.mem (at_ .ecx input)), .mul .edx,
   .alu .add .eax (.mem (at_ .ebp output)), .alu .adc .edx (.imm 0),
   .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp output) .eax, .mov .ebx (.reg .edx)]

end VG.Impl.Mont.X86
