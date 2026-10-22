module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialLoop
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialTable
public import VerifiedGarbage.Impl.Mont.X86.Context

/-! Borrow a small frame around the shared packed-prime filter and restore the workspace pointer. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def trialTableOffset : Nat := 10240
def trialWordCount (n : Nat) : Nat := if 17 ≤ n then 512 else 256

def trialArgPointer (offset index : Nat) : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 offset)),
    .store (at_ .esp (4 * index)) .eax]

def trialArguments (n : Nat) : List Instr :=
  trialArgPointer (Dynamic.slot n 0) 0 ++ trialArgPointer (Dynamic.slot n 0 + 8 * n) 1 ++
    trialArgPointer trialTableOffset 2 ++
    [.mov .eax (.imm (BitVec.ofNat 32 (trialWordCount n))), .store (at_ .esp 12) .eax]

def withTrial (n : Nat) (body : Prog isa) : Prog isa :=
  .frame (.push [.edi])
    (.frame (.alloc 36) (.seq (.block (trialArguments n)) body) (.free 36)) (.pop .edi 1)

def trialFilter (n : Nat) : Prog isa := withTrial n trialLoopEarly

def candidateTrial (n : Nat) : Prog isa :=
  .seq (.block (trialTable trialTableOffset (trialWordCount n))) (trialFilter n)

end VG.Impl.Dsa.X86.Generation
