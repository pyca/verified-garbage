module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Spec.P521

/-!
# Arithmetic modulo P-521's prime `p = 2⁵²¹ - 1`, as functions, on RISC-V

`vg_p521_{mul,add,sub}_mod_p(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`)
for numbers of nine 64-bit words: the functions of any odd modulus of seven
words or more (`Impl/Weierstrass/RISCV64/GenWide.lean`), whose own working
space is the top 576 bytes of `ws`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P521Field

open VG.RISCV64

/-- The function multiplying modulo `p`. -/
def mulFn : Prog isa := GenWide.mulFn 9 Spec.P521.p

/-- The function adding modulo `p`. -/
def addFn : Prog isa := GenWide.addFn 9 Spec.P521.p

/-- The function subtracting modulo `p`. -/
def subFn : Prog isa := GenWide.subFn 9 Spec.P521.p

end VG.Impl.Weierstrass.RISCV64.P521Field
