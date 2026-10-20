module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorPower
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt

/-! Filter a generator input, exponentiate it, and test its result in native code. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def generatorRangeArguments (len : Nat) (result : Bool) : List HeaderArgument :=
  [⟨16, .frame 5 VG.Impl.Dsa.Generation.Layout.p⟩, ⟨17, .literal len⟩,
   ⟨18, if result then .frame 5 VG.Impl.Dsa.Generation.Layout.g else .frame 21 0⟩,
   ⟨19, .literal len⟩]

def generatorRangeFromFrame (len : Nat) (result : Bool) : Prog isa :=
  seqs [.block workspaceBase, workspace (len / 8),
    .block (headerArguments (generatorRangeArguments len result)),
    if result then generatorResult else generatorRange]

def generatorInput : List Instr :=
  [.ldrSp .x0 40, .ldrSp .x3 168, .str .x .x3 .x0 VG.Impl.Dsa.Layout.Field.g.offset]

def generatorEvaluate (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (.block generatorInput) (generatorPowerFresh mul len)

def generatorStep (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (generatorRangeFromFrame len false)
    (.ite (.zero .x .x3) (.block (stackStatus 3))
      (seqs [generatorEvaluate mul len, generatorRangeFromFrame len true,
        .ite (.zero .x .x3) (.block (stackStatus 3)) (.block (stackStatus 1))]))

end VG.Impl.Dsa.AArch64.Generation
