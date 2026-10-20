module

public import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit

/-!
# The AArch64 comb's taint, analysed once

The comb (`vg_ed448_r56_comb_base`) is called by the base-point multiplications of
X448 and Ed448 and by the verifier's `[S]B`. `combSum` analyses it once, without
what the analysis does not read, for all of them (`taint_decide_sum [combSum]`), and
for the comb's own check (`CombBase.comb_check`); `x20`, which the comb does not
write, stays as public as it was. The comb's step is built once, as a literal, which
the summary and the check of the step's stores read.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.AArch64.Base.stepR

end VG

namespace VG.Proof.Ed448.AArch64.CombBase

open VG VG.AArch64 VG.Impl.Ed448.AArch64.CombBase
open VG.Impl.X448.AArch64.Base (combSym)

taint_summary combSum : (taintS [combSym]) (Taint.ofRegs [.x0, .x1]) (Code.eraseT combBaseFn)
  keeping (Taint.ofRegs [.x20])

end VG.Proof.Ed448.AArch64.CombBase
