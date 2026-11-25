module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # A summary of Keccak-f[1600] on two interleaved states, for its callers' constant-time checks -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.X2Sums

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.X2

-- The call without FEAT_SHA3, with the offsets erased.
taint_summary erased : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x19, .x20, .x21, .x22, .x28])
  (.call (name false) (Code.eraseOff (code false)))

end VG.Proof.Sha3.AArch64.Neon.X2Sums
