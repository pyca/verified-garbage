module

public import VerifiedGarbage.Impl.Bignum.X86.WideProduct

/-! # Recombine the CRT coefficient with q and its residue -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

/-- q and h have n 64-bit words; residue and output have 2*n words. -/
def crtRecombine (n product q h residue out mult : Nat) : Prog isa :=
  .seq (wideProduct (2 * n) product q h mult) (chainW .adc (4 * n) out product residue)

end VG.Impl.Bignum.X86
