module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# Montgomery squaring on RISC-V: constant time

`sqrTail_ct`: two runs of `Impl/Bignum/RISCV64/MontSqr.lean`'s `sqrTail`
from states that agree on the bases (`a2`, `a3`, `a5`, `a6`, `a7`), `w`
(`t0`) and the stack pointer take the same path and touch the same
addresses, whatever the numbers and `-m⁻¹` (`t1`) are, as the taint analysis
checks.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- The registers `sqrTail`'s timing may depend on. -/
def sqrPub : List Reg := [.a2, .a3, .a5, .a6, .a7, .t0]

theorem sqrTail_ct :
    RelCT isa (fun s₁ s₂ => taint.Agree (Taint.ofRegs sqrPub) s₁ s₂) sqrTail fun _ _ => True :=
  RelCT.taint _ (fun _ _ h => h) (by taint_decide)

end VG.Proof.Bignum.RISCV64
