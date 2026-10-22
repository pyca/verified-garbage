module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # Candidate reduction reuses RSA's existing division and word operations

Array 0 starts as the shaped hash value X; array 2 contains 2q. Array 5
receives X - X mod (2q) + 1, and array 0 receives twice the quotient, the
generator exponent. The caller initializes the constant header word to 1.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def reductionOne : Nat := 144

def doubleArray (L : Rsa.X86.KeyRt.Lay) (j : Nat) : Prog isa :=
  Rsa.X86.KeyRt.chain L .adc j j j false

def reduceCandidate (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (Rsa.X86.KeyRt.copy L 4 0)
    (.seq (Rsa.X86.KeyRt.div L 0 1 2 3)
      (.seq (Rsa.X86.KeyRt.sub3 L 5 4 1)
        (.seq (.block (Rsa.X86.KeyRt.addLow L 5 reductionOne)) (doubleArray L 0))))

end VG.Impl.Dsa.X86.Generation
