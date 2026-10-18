module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate

/-! Hash, shape and test q using the same callable primality operation as p. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def subgroup (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa))
    (len : Nat) : Prog isa :=
  seqs [qCandidate G1 G256, .block workspaceBase,
    checkPrime mul roundCode 4 VG.Impl.Dsa.Generation.Layout.q len (if len = 20 then 24 else 32) 64,
    .block primeResult]

end VG.Impl.Dsa.AArch64.Generation
