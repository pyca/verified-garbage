module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArithmetic
public import VerifiedGarbage.Impl.Dsa.X86.Bytes

/-! # Decode the shaped candidate and form its even divisor -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86

/-- ESI points to q. The extra word receives the carry when q is doubled. -/
def loadDivisor (qlen n : Nat) : Prog isa :=
  .seq (loadComponent qlen n candidateDivisor)
    (.seq (zeroPad (candidateDivisor + 8 * n) 1)
      (doubleWords (2 * n + 1) candidateDivisor candidateTemporary))

/-- ESI points to the full-width shaped hash suffix. -/
def loadCandidate (plen n : Nat) : Prog isa := loadComponent plen n candidateQuotient
end VG.Impl.Dsa.X86.Generation
