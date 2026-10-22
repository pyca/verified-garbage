module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial

/-! Trial division by the shared packed prime table.

The parent frame's first six words contain the candidate start and end,
the current table pointer, remaining table words, the packed prime pair,
and the accumulated flag. No branch depends on an individual divisor.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def trialStart : Nat := 0
def trialEnd : Nat := 4
def trialTablePtr : Nat := 8
def trialCount : Nat := 12
def trialPair : Nat := 16
def trialResult : Nat := 20

def trialNextPair : List Instr :=
  [.mov .eax (.mem (at_ .esp trialTablePtr)), .mov .ebx (.mem (at_ .eax 0)),
   .store (at_ .esp trialPair) .ebx, .alu .add .eax (.imm 4),
   .store (at_ .esp trialTablePtr) .eax, .alu .and .ebx (.imm 65535)]

def trialAccumulate : List Instr :=
  [.mov .edx (.mem (at_ .esp trialResult)), .alu .or .edx (.reg .eax),
   .store (at_ .esp trialResult) .edx]

def trialHighPrime : List Instr :=
  [.mov .ebx (.mem (at_ .esp trialPair)), .shift .shr .ebx 16]

def trialCountDown : List Instr :=
  [.mov .eax (.mem (at_ .esp trialCount)), .alu .sub .eax (.imm 1),
   .store (at_ .esp trialCount) .eax, .alu .cmp .eax (.imm 0)]

def trialPairStep : Prog isa :=
  .seq (.block trialNextPair)
    (.seq (trialPrime trialStart trialEnd)
      (.seq (.block trialAccumulate)
        (.seq (.block trialHighPrime)
          (.seq (trialPrime trialStart trialEnd)
            (.seq (.block trialAccumulate) (.block trialCountDown))))))

def trialLoopWith (step : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .store (at_ .esp trialResult) .eax])
    (.seq (.loop step .ne) (.block [.mov .eax (.mem (at_ .esp trialResult))]))

def trialLoop : Prog isa := trialLoopWith trialPairStep

/-- Parameter candidates come from the public random tape, so a divisor may stop the filter. -/
def trialPairUntil : Prog isa :=
  .seq trialPairStep (.ite .e (.block [])
    (.block [.mov .eax (.mem (at_ .esp trialResult)), .alu .cmp .eax (.imm 1)]))

def trialLoopEarly : Prog isa := trialLoopWith trialPairUntil

end VG.Impl.Dsa.X86.Generation
