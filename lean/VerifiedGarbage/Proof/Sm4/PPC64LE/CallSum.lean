module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# The constant-time analysis of the PPC64LE modes' calls of SM4, once

Every mode (`Impl/Sm4/PPC64LE/Modes.lean`, `Ctr.lean`, `Ctr32.lean`) calls
`vg_sm4_prepare_keys` at the same taint (`τPrep`): the arguments `r3`–`r7`
and the mode's `r29`–`r31` public, the IV's base in `r29` (and in `r31`),
the scratch buffer's in `r5`, no slot public. It calls
`vg_sm4_crypt_prepared` at another (`τCrypt`), with the scratch buffer's base
in `r5` and `r3`. The analyses of the calls are summaries (`taint_summary`),
which the modes' checks use (`taint_decide_sum`) in place of the analysis
of the functions in each.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE

/-- What the modes have public at their call of `vg_sm4_prepare_keys`. -/
def τPrep : SlotTaint.T :=
  { regs := .ofList [.r3, .r4, .r5, .r6, .r7, .r29, .r30, .r31], lens := [16, 0, 3264],
    bases := [(.r29, 0, 0), (.r5, 2, 0), (.r31, 1, 0)] }

taint_summary prepSum : slotTaint τPrep (.call "vg_sm4_prepare_keys" Impl.Sm4.PPC64LE.prepareKeys)

/-- What the modes have public at their calls of `vg_sm4_crypt_prepared`. -/
def τCrypt : SlotTaint.T :=
  { regs := .ofList [.r3, .r4, .r5, .r6, .r7, .r29, .r30, .r31], lens := [16, 0, 3264],
    bases := [(.r5, 2, 0), (.r3, 2, 0)] }

taint_summary cryptSum : slotTaint τCrypt (.call "vg_sm4_crypt_prepared" Impl.Sm4.PPC64LE.cryptPrepared)

end VG.Proof.Sm4.PPC64LE
