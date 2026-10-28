module

public import VerifiedGarbage.Impl.Mont.X86

/-! # The public exponent's class: even, 1, 65537, or another odd number -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Impl.Mont.X86

def parity : List Instr :=
  [.mov .eax (.mem (sc 128)), .alu .and .eax (.imm 1), .alu .cmp .eax (.imm 0)]

def equal (value : Nat) : List Instr :=
  [.mov .eax (.mem (sc 128)), .alu .xor .eax (.imm (BitVec.ofNat 32 value)),
    .alu .or .eax (.mem (sc 132)), .alu .cmp .eax (.imm 0)]

end VG.Impl.RsaKeyGen.X86.ExponentFilter
