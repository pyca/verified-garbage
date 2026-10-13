module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxTiledSquare
open VG.X86_64

/-- For sizes that pass `Adx.sizeTest`: the triangular tiles if `w` is a
multiple of 8, and the square for four-word groups otherwise. -/
def alignedChoice (o a : Nat) : Prog isa :=
  .seq (.block AdxSquare.redcTest) (.ite .e (montSquare o a) (AdxSquare.montSquare4 o a))

def choice (o a : Nat) : Prog isa :=
  .seq (.block Adx.sizeTest)
    (.ite .e (alignedChoice o a) (X86_64.montMul Public.aN Public.aAcc Public.aTmp o a a))

/-- Aligned squares use triangular tiles; other sizes retain the verified fallbacks. -/
def dispatch (o a b : Nat) : Prog isa :=
  if a=b then choice o a else AdxTiledProduct.choice o a b

end VG.Impl.Bignum.X86_64.AdxTiledSquare
