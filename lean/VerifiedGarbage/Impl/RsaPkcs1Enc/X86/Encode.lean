module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode

/-! # EME encryption block construction on i686

EDI is the output cursor, ESI the padding-string cursor, and EBP its
positive public byte count. EBX accumulates whether any padding byte is
zero. All padding and message bytes are copied without data-dependent
branches.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Enc.X86
open VG VG.X86

def head : List Instr := VG.Impl.RsaPkcs1Sig.X86.putBytes [0, 2] ++ [.mov .ebx (.imm 0)]

def psStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .store8 ⟨.edi, 0⟩ .al,
    .alu .sub .eax (.imm 1), .shift .shr .eax 31, .alu .or .ebx (.reg .eax),
    .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ebp (.imm 1)]

def psLoop : Prog isa := .loop (.block psStep) .ne

def separator : List Instr := VG.Impl.RsaPkcs1Sig.X86.putByte 0

def message : Prog isa :=
  .seq (.block [.alu .cmp .ebp (.imm 0)])
    (.ite .e (.block []) VG.Impl.RsaPkcs1Sig.X86.copyLoop)

/-- Mask each output byte by DL. ESI and ECX are the public pointer/count. -/
def maskStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .alu .and .eax (.reg .edx), .store8 ⟨.esi, 0⟩ .al,
    .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]

def maskLoop : Prog isa := .loop (.block maskStep) .ne

end VG.Impl.RsaPkcs1Enc.X86
