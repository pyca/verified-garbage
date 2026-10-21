module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Set the candidate's low bit and two highest bits -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateBits
open VG VG.X86 VG.Impl.Mont.X86

def forceWord (offset : Nat) (mask : BitVec 32) : List Instr :=
  [.mov .eax (.mem (sc offset)), .alu .or .eax (.imm mask), .store (sc offset) .eax]

def code (w out : Nat) : List Instr :=
  forceWord out 1 ++ forceWord (out + 8 * w - 4) 0xc0000000

end VG.Impl.RsaKeyGen.X86.CandidateBits
