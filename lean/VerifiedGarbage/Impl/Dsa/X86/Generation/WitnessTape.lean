module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawCopy
public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundCall

/-! Retain the next witness cursor before arithmetic reuses the copy registers. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def witnessCursor : Nat := Dsa.Generation.Layout.control + 32
def witnessRemaining : Nat := Dsa.Generation.Layout.control + 36

def rememberDraw (drawBytes : Nat) : List Instr :=
  [.store (sc witnessCursor) .esi, .mov .eax (.mem (sc witnessRemaining)),
    .alu .sub .eax (.imm (BitVec.ofNat 32 drawBytes)), .store (sc witnessRemaining) .eax]

def drawFromTape (len drawBytes : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (sc witnessCursor))])
    (.seq (drawCopy len drawBytes) (.block (rememberDraw drawBytes)))

def drawRound (name : String) (code : Prog isa) (n len drawBytes : Nat) : Prog isa :=
  .seq (drawFromTape len drawBytes) (sampleRound name code n len)

end VG.Impl.Dsa.X86.Generation
