module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Test for a whole witness block before advancing entropy -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessAvailable
open VG VG.X86 VG.Impl.Mont.X86

def code (w : Nat) : List Instr :=
  [.mov .eax (.mem (sc 32)), .alu .sub .eax (.mem (sc 152)),
    .alu .cmp .eax (.imm (BitVec.ofNat 32 (8 * w)))]

end VG.Impl.RsaKeyGen.X86.WitnessAvailable
