module

public import VerifiedGarbage.Impl.X448.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.X448.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# X448 on x86-64: the code as a literal

Materializing the code once avoids rebuilding the unrolled arithmetic in each
kernel-evaluated check. The field operations are templates
(`materialize_template`), each evaluated once with its offsets free rather
than once for every product, sum and swap of the code.
-/

@[expose] public section

namespace VG.Proof.X448.X86_64.Lit
open VG.Impl.X448.X86_64

materialize_template mulT := mul
materialize_template sqrT := sqr
materialize_template a24T := Field.a24 baseline
materialize_template addT := add
materialize_template subT := sub
materialize_template cswapT := cswap

end VG.Proof.X448.X86_64.Lit

namespace VG

materialize_code Impl.X448.X86_64.pow223Fn
materialize_code Impl.X448.X86_64.x448

end VG
