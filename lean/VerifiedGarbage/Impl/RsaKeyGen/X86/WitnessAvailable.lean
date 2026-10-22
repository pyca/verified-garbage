module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Test for a whole witness block before advancing entropy -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessAvailable
open VG VG.X86 VG.Impl.Mont.X86

/-- Whether `D` more octets remain. -/
def codeAt (D : Nat) : List Instr :=
  [.mov .eax (.mem (sc 32)), .alu .sub .eax (.mem (sc 152)),
    .alu .cmp .eax (.imm (BitVec.ofNat 32 D))]

def code (w : Nat) : List Instr := codeAt (8 * w)

end VG.Impl.RsaKeyGen.X86.WitnessAvailable
