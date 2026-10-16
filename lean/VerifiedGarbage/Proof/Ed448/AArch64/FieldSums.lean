module

public import VerifiedGarbage.Impl.X448.AArch64.Field56
meta import VerifiedGarbage.Impl.X448.AArch64.Field56
public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Impl.Ed448.AArch64.Point56
meta import VerifiedGarbage.Impl.Ed448.AArch64.Point56
meta import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
