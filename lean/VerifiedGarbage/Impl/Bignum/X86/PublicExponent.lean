module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.Mont.X86.Exponent

/-! # Fixed-schedule public RSA exponentiation in the compact workspace

The checked public exponent fits in two 32-bit words at header offset 128.
After encoding the base, array five is reused for the conditional product.
The exponent is consumed; its values never select an address or branch.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86

def exponentOffset : Nat := 128
def maskOffset : Nat := 136

def exponentProduct (n : Nat) : Prog isa :=
  .seq (.block (Dynamic.exponentMask exponentOffset maskOffset))
    (.seq (multiply n 5 7 6)
      (Dynamic.selectProduct (modulus n) (slot n 7) (slot n 5) maskOffset))

def exponentBody (n : Nat) : Prog isa :=
  .seq (exponentProduct n)
    (.seq (multiply n 6 6 6) (.block (Dynamic.shiftExponent 2 exponentOffset)))

def exponentStep (n : Nat) : Prog isa :=
  .seq (exponentBody n) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- Input in array six; output in array seven. One and R² come from setup. -/
def exponentiate (n : Nat) : Prog isa :=
  .seq (multiply n 7 5 4)
    (.seq (multiply n 6 6 5)
      (.seq (.block [.mov .esi (.imm 64)])
        (.seq (.loop (exponentStep n) .ne) (multiply n 7 7 4))))

end VG.Impl.Bignum.X86.PublicContext
