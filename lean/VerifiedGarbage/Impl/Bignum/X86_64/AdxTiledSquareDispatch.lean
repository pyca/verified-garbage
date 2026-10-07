import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare

namespace VG.Impl.Bignum.X86_64.AdxTiledSquare
open VG.X86_64

def alignedChoice (o a : Nat) : Prog isa :=
  .seq (.block AdxSquare.redcTest) (.ite .e (montSquare o a) (AdxSquare.montSquare o a))

def choice (o a : Nat) : Prog isa :=
  .seq (.block Adx.sizeTest) (.ite .e (alignedChoice o a) (Adx.montMulAdx o a a))

/-- Aligned squares use triangular tiles; other sizes retain the verified fallbacks. -/
def dispatch (o a b : Nat) : Prog isa :=
  if a=b then choice o a else AdxTiledProduct.choice o a b

end VG.Impl.Bignum.X86_64.AdxTiledSquare
