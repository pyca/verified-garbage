module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Zero-extended constants for private RSA arithmetic -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86

def smallConstant (n out value : Nat) : Prog isa :=
  .seq (Dynamic.zerosW out (2 * n))
    (.block [.mov .eax (.imm (BitVec.ofNat 32 value)), .store (sc out) .eax])

end VG.Impl.Bignum.X86
