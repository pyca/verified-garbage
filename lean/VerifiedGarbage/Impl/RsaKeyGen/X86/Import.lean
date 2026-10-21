module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Whole-word big-endian imports for candidates and witnesses

Candidate and witness lengths are positive multiples of eight bytes.
Native loads and BSWAP therefore import four bytes per iteration without
padding or per-byte work. ESI starts at the input, EBX at the destination's
last native word, and ECX is the native-word count. EDI is preserved.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Import
open VG VG.X86

def at_ (r : Reg) : MemOp := ⟨r, 0⟩

def step : List Instr :=
  [.mov .eax (.mem (at_ .esi)), .bswap .eax, .store (at_ .ebx) .eax,
    .alu .add .esi (.imm 4), .alu .sub .ebx (.imm 4), .alu .sub .ecx (.imm 1)]

def code : Prog isa := .loop (.block step) .ne

end VG.Impl.RsaKeyGen.X86.Import
