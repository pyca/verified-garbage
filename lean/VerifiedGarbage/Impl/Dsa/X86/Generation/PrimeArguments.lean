module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Prime
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialCheck

/-! # Bridge persistent candidate and witness slots to the native prime engine -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

def primeInputArgs : List Instr := workspaceBase ++ [.mov .esi (.mem (frameSlot 22))]

def frameToWorkspace (index offset : Nat) : List Instr :=
  [.mov .eax (.mem (frameSlot index)), .store (sc offset) .eax]

def primeTapeArgs : List Instr :=
  frameToWorkspace 13 primeTape ++ frameToWorkspace 15 primeTapeLen ++ frameToWorkspace 16 primeUsed ++
  bufferPointer .eax VG.Impl.Dsa.Generation.Layout.witness ++ [.store (sc primeWitness) .eax]

def workspaceToFrame (offset index : Nat) : List Instr :=
  [.mov .eax (.mem (sc offset)), .store (frameSlot index) .eax]

def primeReturn : List Instr := workspaceToFrame primeUsed 16 ++ workspaceToFrame primeStatus 19

def primeSetupFromFrame (len : Nat) : Prog isa :=
  .seq (.block primeInputArgs)
    (.seq (loadComponent len ((len + 7) / 8) (slot ((len + 7) / 8) 0)) (.block primeTapeArgs))

/-- This is entered only after trial division accepts the candidate. -/
def primeFromFrame (len : Nat) : Prog isa :=
  .seq (primeSetupFromFrame len) (.seq (primeTest len) (.block primeReturn))

def trialArgs : List Instr := [.mov .esi (.mem (frameSlot 22)), .mov .edi (.mem (frameSlot 5))]

def trialFromFrame (len : Nat) : Prog isa :=
  .seq (.block trialArgs) (trialCheck len (if len ≤ 128 then 512 else 1024))

/-- The reciprocal trial table is initialized once per parameter-generation call. -/
def checkPrime (len : Nat) : Prog isa :=
  .seq (trialFromFrame len)
    (.seq (.block [.alu .cmp .eax (.imm 1)])
      (.ite .e (primeFromFrame len) (.block (frameStatus 3))))
end VG.Impl.Dsa.X86.Generation
