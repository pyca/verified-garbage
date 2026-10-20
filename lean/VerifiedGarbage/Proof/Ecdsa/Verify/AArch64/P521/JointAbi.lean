module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Ecdsa.AArch64

theorem verify_callsKeep : CallsKeep verifyP521 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP521 := by lit_decide

theorem verify_keepsV : verifyP521.allInstrs keepsV = true := by lit_decide

end VG.Proof.Ecdsa.Verify.AArch64.P521
