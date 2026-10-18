module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate

/-! # Hash, shape and test a subgroup-prime candidate in native code -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Bignum.X86_64 (seqs)

def subgroup (G1 G256 : Stream) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) (len : Nat) : Prog isa :=
  seqs [qCandidate G1 G256, .block workspaceBase,
    checkPrime mul round 4 VG.Impl.Dsa.Generation.Layout.q len (if len = 20 then 24 else 32) 64,
    .block primeResult]

end VG.Impl.Dsa.X86_64.Generation
