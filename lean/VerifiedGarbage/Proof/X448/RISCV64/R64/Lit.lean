module

public import VerifiedGarbage.Impl.X448.RISCV64.R64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X448.RISCV64.R64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# Curve448's field on RISC-V, 64-bit limbs: the code as literals

The products, squares and reductions are built from lists of terms that the
generators index and measure at every term (`tm`, `pstart`), which the
kernel evaluates slowly, at every product of every check that evaluates code
with them (`taint_decide`, `lit_decide`): X448's ladder and inversion, and
Ed448's point operations, which inline them. They are functions of their
operands' offsets alone, as the sums, the differences and the swap are, so
each is a template (`materialize_template`), evaluated once with its offsets
free; the code that contains them then adds the offsets. The inversion's shared chain and what the two entry points of
X448 share are literals (`materialize_code`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64.Lit
open VG.Impl.X448.RISCV64.R64

materialize_template productT := product
materialize_template squareT := square
materialize_template reduceT := reduce
materialize_template addT := add
materialize_template subT := sub
materialize_template cswapT := cswap

end VG.Proof.X448.RISCV64.R64.Lit

namespace VG

materialize_code Impl.X448.RISCV64.R64.chain223Shared
materialize_code Impl.X448.RISCV64.R64.tail

end VG
