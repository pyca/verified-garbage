module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPrecomputed
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall

/-! # The private CRT, its window's products calls to a shared Montgomery product

`mul` is the product's code and `name` its symbol (`vg_rsa_mont_mul` and its
variants): the window's multiplications and squares, and the CRT's other
products, are each a call (`MontCall.op`), not a copy of the product. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.CrtCall
open VG VG.Arm

def phase (name : String) (mul : Prog isa) : Prog isa := SharedWindow.phase (MontCall.op name mul)
def code (name : String) (mul : Prog isa) : Prog isa := CrtFn.codeWith (phase name mul) (MontCall.op name mul)
def codeGiven (name : String) (mul : Prog isa) (dbl : Prog isa) : Prog isa :=
  CrtFn.codeGiven (phase name mul) (MontCall.op name mul) dbl

end VG.Impl.Bignum.Arm.CrtCall
