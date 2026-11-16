module

public import VerifiedGarbage.Impl.X448.PPC64LE
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X448.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit


/-!
# Curve448's field on PPC64LE: the code as templates

The products, sums, differences and swaps are functions of their operands'
offsets alone, built from lists of terms and registers that the kernel would
evaluate again at every one of them in every check that evaluates code with
them (`taint_decide`, `lit_decide`). Each is a template
(`materialize_template`), evaluated once with its offsets free; the code
that contains them then adds the offsets.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE.Lit
open VG.Impl.X448.PPC64LE

materialize_template mulXT := mulX
materialize_template addT := add
materialize_template subT := sub
materialize_template cswapT := cswap

end VG.Proof.X448.PPC64LE.Lit
