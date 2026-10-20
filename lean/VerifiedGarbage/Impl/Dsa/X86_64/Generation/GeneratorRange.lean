module

public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-! # Native rejection of generator inputs outside 1 < h < p−1 -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

/-- Header words 16/17 and 18/19 hold p and h byte slices. -/
def generatorLoadPair : Prog isa :=
  .seq (seqs (loadA 0 16 17)) (seqs (loadA 1 18 19))

def generatorRange : Prog isa :=
  .seq generatorLoadPair (.seq (.block (decA 0)) (Checks.rangeMask true))

/-- A modular result is accepted precisely when it exceeds one. -/
def generatorResult : Prog isa :=
  .seq generatorLoadPair (Checks.rangeMask true)

end VG.Impl.Dsa.X86_64.Generation
