module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Consume one whole candidate-width entropy block for a witness -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessAdvance
open VG VG.X86 VG.Impl.Mont.X86

def usedOffset : Nat := 152

/-- The next `D` octets. -/
def codeAt (D : Nat) : List Instr :=
  [.mov .esi (.mem (sc 28)), .mov .eax (.mem (sc usedOffset)), .alu .add .esi (.reg .eax),
    .alu .add .eax (.imm (BitVec.ofNat 32 D)), .store (sc usedOffset) .eax]

def code (w : Nat) : List Instr := codeAt (8 * w)

end VG.Impl.RsaKeyGen.X86.WitnessAdvance
