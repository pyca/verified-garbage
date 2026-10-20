module
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Layout
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys


/-! Classify the truncated witness using the shared RSA range comparison. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def witnessRange : Prog isa :=
  seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]

def testRange : Prog isa :=
  .seq witnessRange (.block [sth .x9 kU])

end VG.Impl.Dsa.AArch64.Generation
