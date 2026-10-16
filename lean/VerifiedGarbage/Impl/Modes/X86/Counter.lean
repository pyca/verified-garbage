module

public import VerifiedGarbage.TCB.X86.Isa

/-! # A 128-bit big-endian counter increment on x86 -/

@[expose] public section

namespace VG.Impl.Modes.X86

open VG.X86

/-- Increment the counter at `base + off`, using only `eax` and the flags.
Loads, stores and byte swaps preserve the carry between successive words. -/
def incAt (base : Reg) (off : Nat) : List Instr :=
  [.mov .eax (.mem ⟨base, off + 12⟩), .bswap .eax, .alu .add .eax (.imm 1),
   .bswap .eax, .store ⟨base, off + 12⟩ .eax,
   .mov .eax (.mem ⟨base, off + 8⟩), .bswap .eax, .alu .adc .eax (.imm 0),
   .bswap .eax, .store ⟨base, off + 8⟩ .eax,
   .mov .eax (.mem ⟨base, off + 4⟩), .bswap .eax, .alu .adc .eax (.imm 0),
   .bswap .eax, .store ⟨base, off + 4⟩ .eax,
   .mov .eax (.mem ⟨base, off⟩), .bswap .eax, .alu .adc .eax (.imm 0),
   .bswap .eax, .store ⟨base, off⟩ .eax]

end VG.Impl.Modes.X86
