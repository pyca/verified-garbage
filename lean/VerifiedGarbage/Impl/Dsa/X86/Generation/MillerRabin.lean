module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.WitnessTape
public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundPolicy

/-! Stream witnesses until the shared policy finishes or the supplied tape ends. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def tapeCheck (drawBytes : Nat) : List Instr :=
  [.mov .eax (.mem (sc witnessRemaining)), .alu .cmp .eax (.imm (BitVec.ofNat 32 drawBytes))]

def primeLoopInit : List Instr := setHeader roundIndex 1 ++ setHeader uniformCount 0 ++ setHeader primeStatus 4

def primeLoopEnd : List Instr := [.mov .eax (.mem (sc primeStatus)), .alu .cmp .eax (.imm 4)]

def testedDraw (name : String) (code : Prog isa) (n len drawBytes checks : Nat) : Prog isa :=
  .seq (drawRound name code n len drawBytes) (roundTail checks)

def primeIteration (body : Prog isa) (drawBytes : Nat) : Prog isa :=
  .seq (.block (tapeCheck drawBytes))
    (.seq (.ite .b (.block (setHeader primeStatus 0)) body) (.block primeLoopEnd))

def millerRabin (name : String) (code : Prog isa) (n len drawBytes checks : Nat) : Prog isa :=
  .seq (.block primeLoopInit) (.loop (primeIteration (testedDraw name code n len drawBytes checks) drawBytes) .e)

end VG.Impl.Dsa.X86.Generation
