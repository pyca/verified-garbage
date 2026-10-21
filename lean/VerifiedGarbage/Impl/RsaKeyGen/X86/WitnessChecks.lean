module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Mont.X86

/-! # Initialize the blinded and uniform witness policy for the candidate width -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessChecks
open VG VG.X86 VG.Impl.Mont.X86

def checks (w : Nat) : Nat :=
  if w < 5 then 27 else if w < 6 then 8 else if w < 7 then 7 else if w < 8 then 6 else
    if w < 22 then 5 else if w < 59 then 4 else 3

def code (w : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (sc 176) .eax, .store (sc 192) .eax,
    .mov .eax (.imm (BitVec.ofNat 32 (checks w))), .store (sc 200) .eax]

end VG.Impl.RsaKeyGen.X86.WitnessChecks
