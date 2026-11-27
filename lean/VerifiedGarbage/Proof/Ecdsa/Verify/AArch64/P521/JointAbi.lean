module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombCall
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Ecdsa.AArch64

/-- The three checks below, in one walk of the code. -/
private theorem verify_abi : CallsKeepN verifyP521 ∧ KeepsUntouched verifyP521 ∧
    verifyP521.allInstrs keepsV = true := by lit_decide

theorem verify_callsKeep : CallsKeepN verifyP521 := verify_abi.1

theorem verify_untouched : KeepsUntouched verifyP521 := verify_abi.2.1

theorem verify_keepsV : verifyP521.allInstrs keepsV = true := verify_abi.2.2

end VG.Proof.Ecdsa.Verify.AArch64.P521
