module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorPower
public import VerifiedGarbage.Impl.Dsa.X86.Bytes

/-! # Evaluate a range-checked generator with the saved quotient exponent -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

def generatorEvaluate (len : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (loadComponent len n (slot n 8)) (generatorPower n)
end VG.Impl.Dsa.X86.Generation
