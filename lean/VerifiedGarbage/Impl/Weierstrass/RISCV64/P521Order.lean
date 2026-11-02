module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Spec.P521

/-!
# Arithmetic modulo P-521's order `n`, as functions, on RISC-V

`vg_p521_{mul,add,sub}_mod_n(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`)
for numbers of nine 64-bit words: the functions of any odd modulus of seven
words or more (`Impl/Weierstrass/RISCV64/GenWide.lean`), whose own working
space is the top 576 bytes of `ws`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P521Order

open VG.RISCV64

/-- The function multiplying modulo `n`. -/
def mulFn : Prog isa := GenWide.mulFn 9 Spec.P521.n

/-- The function adding modulo `n`. -/
def addFn : Prog isa := GenWide.addFn 9 Spec.P521.n

/-- The function subtracting modulo `n`. -/
def subFn : Prog isa := GenWide.subFn 9 Spec.P521.n

end VG.Impl.Weierstrass.RISCV64.P521Order
