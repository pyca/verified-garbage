module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Summaries of the block functions' calls

The constant-time check of each mode analysed the block function at its
call; here each block function's call is summarized once
(`taint_summary`), from its arguments public, keeping public the
callee-saved registers, and the modes' checks use the summaries
(`taint_decide_sum`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64

/-- The callee-saved registers the block functions do not write (they save and
restore `x19`–`x22`, which the analysis cannot follow). -/
def callee : List Reg := [.x23, .x24, .x25, .x26, .x27, .x28]

taint_summary encSum : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2])
  (.call "vg_triple_des_encrypt_block" Impl.TripleDes.AArch64.encryptBlock)
  keeping (VectorTaint.ofRegs callee)

taint_summary decSum : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2])
  (.call "vg_triple_des_decrypt_block" Impl.TripleDes.AArch64.decryptBlock)
  keeping (VectorTaint.ofRegs callee)

end VG.Proof.TripleDes.AArch64
