module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PreparePrime
public import VerifiedGarbage.Impl.Dsa.X86.Generation.MillerRabin
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialFilter
public import VerifiedGarbage.Spec.Dsa

/-! Filter public candidates before preparing their shared Miller–Rabin context. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def witnessDrawBytes (len : Nat) : Nat := 8 * ((len + 7) / 8)

def testCandidate (name : String) (code : Prog isa) (n len : Nat) : Prog isa :=
  .seq (preparePrime n (8 * len))
    (millerRabin name code n len (witnessDrawBytes len) (Spec.Dsa.primeChecks (8 * len)))

def probablePrime (name : String) (code : Prog isa) (n len : Nat) : Prog isa :=
  .seq (candidateTrial n) (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .e (testCandidate name code n len) (.block (setHeader primeStatus 3))))

end VG.Impl.Dsa.X86.Generation
