module

public import VerifiedGarbage.Impl.Ed448.AArch64.Point56
meta import VerifiedGarbage.Impl.Ed448.AArch64.Point56
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# The taint of the AArch64 point addition and power, analysed once

The base-point multiplications of X448 and Ed448 both call the point addition
(`vg_ed448_r56_point_add`, twice, combining the comb's halves) and the power
(`vg_gf448_r56_pow_p34`, inverting `z`). Their checks analysed both callees each;
`addSum` and `powSum` analyse each once, without what the analysis does not read,
for both (`taint_decide_sum [combSum, addSum, powSum]`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Point56
open VG.Impl.X448.AArch64.Base (combSym)

taint_summary addSum : (taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x3, .x12, .x20]) (Code.eraseT addFn)
taint_summary powSum : (taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x3, .x12, .x20]) (Code.eraseT powFn)

end VG.Proof.Ed448.AArch64
