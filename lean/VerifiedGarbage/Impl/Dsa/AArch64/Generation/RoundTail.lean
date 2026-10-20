module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Layout
import VerifiedGarbage.Impl.Rsa.AArch64.CarrySelect
import VerifiedGarbage.Impl.Rsa.AArch64.Keys


/-! RSA's blinded-round policy with the caller's uniform-witness target. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def roundTail : Prog isa :=
  seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 3, sth .x3 kStat])
        (.block [ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1, .logic .and .x .x4 .x4 .x5,
          ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni,
          movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5, .csel .x .x13 .x10 .x9, ldh .x5 kChecks,
          .subs .x .x6 .x4 .x5, .csel .x .x13 .x13 .x9, sth .x13 kStat])]

end VG.Impl.Dsa.AArch64.Generation
