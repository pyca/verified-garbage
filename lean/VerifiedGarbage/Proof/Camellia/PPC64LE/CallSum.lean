module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# The constant-time analysis of the PPC64LE modes' calls of Camellia, once

Every mode (`Impl/Camellia/PPC64LE/Modes.lean`) calls
`vg_camellia_crypt_prepared` at the same taint (`τCrypt`): the arguments
`r3`–`r5`, the modes' `r28`–`r31`, `r6`, `r7` and `r10` public, the scratch
buffer's base in `r4` and in `r6`, no slot public. The analysis of the call
is a summary (`taint_summary`), which the modes' checks use
(`taint_decide_sum`) in place of the analysis of the function in each.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE

/-- What the modes have public at their calls of `vg_camellia_crypt_prepared`. -/
def τCrypt : SlotTaint.T :=
  { regs := .ofList [.r3, .r4, .r5, .r6, .r7, .r10, .r28, .r29, .r30, .r31], lens := [16, 0, 3376],
    bases := [(.r6, 2, 0), (.r4, 2, 0)] }

taint_summary cryptSum : slotTaint τCrypt
  (.call (Spec.Camellia.Prepared.cryptApi Impl.Camellia.PPC64LE.layout).name Impl.Camellia.PPC64LE.cryptPrepared)

end VG.Proof.Camellia.PPC64LE
