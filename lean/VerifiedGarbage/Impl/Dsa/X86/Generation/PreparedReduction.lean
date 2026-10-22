module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Reduce
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Header
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace

/-! Double the staged subgroup, clear its division tail, and reuse RSA candidate reduction. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def divisorTop (words : Nat) : Nat := Rsa.X86.Keys.slot words 2 + 4 * words

def preparedReduction (words : Nat) : Prog isa :=
  .seq (.block (setHeader reductionOne 1))
    (.seq (doubleArray arithmeticLay 2)
      (.seq (.block (setHeader (divisorTop words) 0)) (reduceCandidate arithmeticLay)))

end VG.Impl.Dsa.X86.Generation
