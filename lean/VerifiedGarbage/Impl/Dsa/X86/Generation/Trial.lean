module
public import VerifiedGarbage.Impl.Mont.X86

/-! # Division-free trial reduction for small primes

ESI holds the divisor, EDI its floor(2^32/divisor) reciprocal, and EBX the
single-word dividend. Two multiplications estimate the remainder, and a
masked correction makes it canonical. Trial chunks are 16 bits, so all
intermediate dividends fit in 32 bits for the table's primes through 8161.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def smallRemainder : List Instr :=
  [.mov .eax (.reg .ebx), .mul .edi, .mov .eax (.reg .edx), .mul .esi,
   .alu .sub .ebx (.reg .eax), .alu .sub .ebx (.reg .esi), .alu .sbb .eax (.reg .eax),
   .alu .and .eax (.reg .esi), .alu .add .ebx (.reg .eax)]

/-- EBP points to a big-endian two-byte chunk. ECX counts the chunks. -/
def trialChunk : List Instr :=
  [.movzx8 .eax (at_ .ebp 0), .shift .ror .eax 24,
   .movzx8 .edx (at_ .ebp 1), .alu .add .eax (.reg .edx),
   .shift .ror .ebx 16, .alu .add .ebx (.reg .eax)] ++ smallRemainder ++
  [.alu .add .ebp (.imm 2), .alu .sub .ecx (.imm 1)]

/-- Nonempty, even-length candidates; no candidate-dependent branches. -/
def trialReduce : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0)]) (.loop (.block trialChunk) .ne)
end VG.Impl.Dsa.X86.Generation
