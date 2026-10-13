module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Bignum.Crt VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt

def pPhase (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsP ++ [.block [enterP]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], zeroArr aX,
    .block [ldh .x5 sWsQ, ldw .x16 .x5 (sArr aY), ldw .x12 .x5 sW, ldh .x17 (sArr aX)],
    copyWords, mul aX aX aR2, mul aX aX aY, mul aY aXm aY, .block [enterP]] ++
  redc mul aY ++ [expLoop window mul select sDp sPlen] ++ [.block [leave]] ++ [.block [enterP]] ++ redc mul aX ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]


def main (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ VG.Impl.Rsa.AArch64.WindowFive.primesSetup ++ checks ++
    VG.Impl.Rsa.AArch64.WindowFive.qPhase window mul select ++ pPhase window select mul ++ VG.Impl.Rsa.AArch64.Crt.finish)

end VG.Impl.Rsa.AArch64.WindowFive
