module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Big-endian counter increments on x86: of 128 bits, and of GCM's last 32 -/

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

/-- Increment the 32-bit big-endian word at `base + off` modulo 2³² (GCM's
`inc₃₂` on a counter block's last word), using only `eax` and the flags. -/
def inc32At (base : Reg) (off : Nat) : List Instr :=
  [.mov .eax (.mem ⟨base, off⟩), .bswap .eax, .alu .add .eax (.imm 1), .bswap .eax, .store ⟨base, off⟩ .eax]

end VG.Impl.Modes.X86
