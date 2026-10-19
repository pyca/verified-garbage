module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Copy disjoint little-endian arrays within the RSA workspace -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def copyArray (n src dst : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) (selectsW (2 * n) src src dst)

end VG.Impl.Bignum.X86
