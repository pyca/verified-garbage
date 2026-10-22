module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.ReduceAt
public import VerifiedGarbage.Impl.Dsa.X86.Core

/-! Stage X and q, reduce through RSA arithmetic, and serialize p and its generator exponent. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def reductionInputTransfers (n : Nat) : List WordTransfer :=
  [{ words := 2 * n, destination := Dsa.Generation.Layout.arithmetic + Rsa.X86.Keys.slot (2 * n) 0,
     source := slot n 0 },
   { words := 2 * n, destination := Dsa.Generation.Layout.arithmetic + Rsa.X86.Keys.slot (2 * n) 2,
     source := slot n 2 }]

def reductionOutputTransfers (n : Nat) : List WordTransfer :=
  [{ words := 2 * n, destination := slot n 6,
     source := Dsa.Generation.Layout.arithmetic + Rsa.X86.Keys.slot (2 * n) 5 },
   { words := 2 * n, destination := slot n 8,
     source := Dsa.Generation.Layout.arithmetic + Rsa.X86.Keys.slot (2 * n) 0 }]

def stageReduction (n qLen : Nat) : Prog isa :=
  .seq (Dsa.X86.Core.load n (8 * n) (slot n 0) (.local Dsa.Generation.Layout.shaped))
    (.seq (Dsa.X86.Core.load n qLen (slot n 2) (.local Dsa.Generation.Layout.q))
      (transferWords (reductionInputTransfers n)))

def saveReduction (n : Nat) : Prog isa :=
  .seq (transferWords (reductionOutputTransfers n))
    (.seq (Dsa.X86.Core.store (8 * n) Dsa.Generation.Layout.p)
      (Dsa.X86.Core.storeAt (8 * n) (slot n 8) Dsa.Generation.Layout.exponent))

def pReduce (n qLen : Nat) : Prog isa :=
  .seq (stageReduction n qLen) (.seq (reduceAt n) (saveReduction n))

end VG.Impl.Dsa.X86.Generation
