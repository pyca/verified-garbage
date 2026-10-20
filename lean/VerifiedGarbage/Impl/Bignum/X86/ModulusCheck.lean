module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Check RSA modulus bounds on i686

`esi` names the big-endian modulus and `ecx` is its public length, from
64 through 1024 bytes. ZF is set exactly for a valid modulus.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def modulusRead : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .mov .ebx (.reg .esi), .alu .add .ebx (.reg .ecx),
   .alu .sub .ebx (.imm 1), .movzx8 .edx ⟨.ebx, 0⟩]

def modulusBounds : List Instr :=
  [.mov .ebx (.reg .eax), .alu .sub .ebx (.imm 1), .shift .shr .ebx 31,
   .mov .ebp (.reg .ecx), .alu .sub .ebp (.imm 64), .shift .ror .ebp 24,
   .alu .add .ebp (.reg .eax), .alu .sub .ebp (.imm 128), .shift .shr .ebp 31]

def modulusFinish : List Instr :=
  [.alu .and .edx (.imm 1), .alu .xor .edx (.imm 1), .alu .or .ebx (.reg .edx),
   .alu .or .ebx (.reg .ebp), .alu .cmp .ebx (.imm 0)]

def modulusCheck : List Instr := modulusRead ++ modulusBounds ++ modulusFinish

end VG.Impl.Bignum.X86
