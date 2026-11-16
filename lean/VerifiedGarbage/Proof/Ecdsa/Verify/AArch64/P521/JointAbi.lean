module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Ecdsa.AArch64

/-- The three checks below, in one walk of the code. -/
private theorem verify_abi : AbiOk verifyP521 := by lit_decide

theorem verify_callsKeep : CallsKeep verifyP521 := verify_abi.callsKeep

theorem verify_untouched : KeepsUntouched verifyP521 := verify_abi.untouched

theorem verify_keepsV : verifyP521.allInstrs keepsV = true := verify_abi.keepsV

end VG.Proof.Ecdsa.Verify.AArch64.P521
