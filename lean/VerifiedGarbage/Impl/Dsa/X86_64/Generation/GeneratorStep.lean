module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorRange
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt

/-! # One generator input is filtered, exponentiated, and accepted natively -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def generatorRangeArguments (len : Nat) (result : Bool) : List HeaderArgument :=
  [⟨16, .frame 5 VG.Impl.Dsa.Generation.Layout.p⟩, ⟨17, .literal len⟩,
   ⟨18, if result then .frame 5 VG.Impl.Dsa.Generation.Layout.g else .frame 21 0⟩,
   ⟨19, .literal len⟩]

def generatorRangeFromFrame (len : Nat) (result : Bool) : Prog isa :=
  seqs [.block workspaceBase, workspace (len / 8),
    .block (headerArguments (generatorRangeArguments len result)),
    if result then generatorResult else generatorRange]

/-- Select the parent workspace and bind the current h input. -/
def generatorInput : List Instr :=
  [.mov .rdi (.mem (sp 40)), .mov .rax (.mem (sp 168)), .store (Core.field .g) .rax]

def generatorEvaluate (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (.block generatorInput) (generatorPowerFresh sq mul len)

def generatorStep (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (generatorRangeFromFrame len false)
    (.seq (.block [.alu .test .rax (.reg .rax)])
      (.ite .e (.block (stackStatus 3))
        (seqs [generatorEvaluate sq mul len, generatorRangeFromFrame len true,
          .block [.alu .test .rax (.reg .rax)],
          .ite .e (.block (stackStatus 3)) (.block (stackStatus 1))])))

end VG.Impl.Dsa.X86_64.Generation
