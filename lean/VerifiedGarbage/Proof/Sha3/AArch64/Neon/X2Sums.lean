module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# The paired Keccak without the SHA-3 extension: its call's taint, analysed once

ML-KEM's samplers call `vg_keccak_f1600_x2` in loops whose constant time is
checked on the code with its offsets erased (`Code.eraseOff`), by the
vector-aware analysis, which follows the callee-saved registers the function
keeps in vector registers. Each check analysed the function's two
permutations again. Here the call is summarized (`taint_summary`) from what
its callers have public, and their checks use the summary
(`taint_decide_sum`). The function writes every callee-saved register and
restores it, so the summary has no frame: the registers it leaves public are
those of its own `pre`, which every one of these callers has public.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.X2Sums

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Neon

/-! From the pointers of the states and of the two streams, the count and the frame. -/
taint_summary erased : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x19, .x20, .x21, .x22, .x28])
  (.call (X2.name false) (Code.eraseOff (X2.code false)))

end VG.Proof.Sha3.AArch64.Neon.X2Sums
