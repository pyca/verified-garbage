module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.TCB.X86.Isa

/-! # Accumulate the blinded and uniform witness counts before choosing status -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.Impl.Mont.X86

def roundsOffset : Nat := 176
def uniformOffset : Nat := 192
def checksOffset : Nat := 200
def statusOffset : Nat := 168

def next : List Instr :=
  [.mov .esi (.reg .eax), .mov .eax (.mem (sc roundsOffset)), .alu .add .eax (.imm 1),
    .store (sc roundsOffset) .eax, .mov .ebx (.mem (sc 144)), .alu .and .ebx (.imm 1),
    .alu .add .ebx (.mem (sc uniformOffset)), .store (sc uniformOffset) .ebx,
    .mov .edx (.mem (sc checksOffset))]

def code : Prog isa :=
  .seq (.block next) (.seq (.block WitnessStatus.code) (.block [.store (sc statusOffset) .ecx]))

end VG.Impl.RsaKeyGen.X86.WitnessCount
