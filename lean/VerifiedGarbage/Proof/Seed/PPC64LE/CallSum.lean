module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
meta import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# The constant-time analysis of the PPC64LE modes' calls of SEED, once

Every mode (`Impl/Seed/PPC64LE/Modes.lean`) calls `vg_seed_encrypt_blocks`
or `vg_seed_decrypt_blocks` at the same taint (`τCall`): the arguments
`r3`–`r6`, `r7` and the modes' `r29`–`r31` public, the buffer's block in
`r4` and the working space in `r6` at known offsets of the scratch buffer,
no slot public. The analysis of each call is a summary (`taint_summary`),
which the modes' checks use (`taint_decide_sum`) in place of the analysis of
the function in each.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

/-- What the modes have public at their calls of the blocks functions. -/
def τCall : SlotTaint.T :=
  { regs := .ofList [.r3, .r4, .r5, .r6, .r7, .r29, .r30, .r31], lens := [16, 0, 8 * 144],
    bases := [(.r4, 2, 8 * 136), (.r6, 2, 0)] }

taint_summary encryptSum : slotTaint τCall (Impl.Seed.PPC64LE.blockCall .encrypt)
taint_summary decryptSum : slotTaint τCall (Impl.Seed.PPC64LE.blockCall .decrypt)

end VG.Proof.Seed.PPC64LE
