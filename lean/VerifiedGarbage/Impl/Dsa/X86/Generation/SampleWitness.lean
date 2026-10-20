module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TestWitness
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ForceWitness
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round

/-! # Classify the full-width draw, forcing and reloading only out-of-range values -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

def sampleHead (len : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (loadComponent len n (slot n 5)) (.seq (roundMinusOne n) (testWitness n))

def sampleWitness (len : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (sampleHead len)
    (.ite .e (.seq (.block (forceWitness len)) (loadComponent len n (slot n 5))) (.block []))
end VG.Impl.Dsa.X86.Generation
