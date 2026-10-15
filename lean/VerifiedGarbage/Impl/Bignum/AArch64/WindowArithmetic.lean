module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowLazy

@[expose] public section
namespace VG.Impl.Bignum.AArch64.WindowArithmetic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def reduce (o : Nat) (lazy : Bool) : Prog isa :=
 .seq BlockedRedc.redc (.seq (.block (Square.finishBases o))
   (if lazy then WindowLazy.code else FastFinish.code))

def square (a : Nat) : Prog isa := .seq (WindowRaw.square a) (reduce a true)
def product (o a b : Nat) : Prog isa := .seq (WindowRaw.product a b) (reduce o false)

end VG.Impl.Bignum.AArch64.WindowArithmetic
