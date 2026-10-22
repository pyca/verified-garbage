module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PreparedReduction
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimePreparation

/-! Borrow the arithmetic subspace for modulus-candidate reduction. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def reduceAt (n : Nat) : Prog isa :=
  .seq (.block (enterArithmetic ++ [.mov .esi (.imm (BitVec.ofNat 32 (8 * n)))]))
    (.seq (withArithmetic (preparedReduction (2 * n))) (.block leaveArithmetic))

end VG.Impl.Dsa.X86.Generation
