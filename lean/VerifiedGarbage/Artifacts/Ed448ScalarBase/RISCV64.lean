module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 base-point multiplication on RISC-V

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448ScalarBase.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.scalarBaseApi.artifact RISCV64.target {
    notes := ["Uses only caller-saved registers and no stack. The function expands the scalar's 456 bits \
      into bytes, then runs two iterations of the same code for each bit from the top: RFC 8032's \
      projective addition of `R` and a point selected with a mask, `R` itself in the first (a \
      doubling) and the base point in the second, and the sum swapped into `R` with a mask, \
      always in the first and when the bit is set in the second. Field elements are fourteen \
      32-bit limbs in `scratch` (rounded up to a multiple of 8), with `vg_x448`'s multiplication, \
      addition and subtraction; `Z` is inverted with X448's addition chain for `p - 2`."]
    code := Impl.Ed448.RISCV64.scalarBase
    verified := Proof.Ed448.RISCV64.scalarBase_verified Proof.Ed448.baseLadder2_ok }]

end VG.Artifacts.Ed448ScalarBase.RISCV64
