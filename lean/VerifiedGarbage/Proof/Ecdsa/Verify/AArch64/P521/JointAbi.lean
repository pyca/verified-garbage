module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Ecdsa.AArch64

theorem verify_callsKeep : CallsKeep verifyP521 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP521 := by lit_decide

theorem verify_keepsV : verifyP521.allInstrs keepsV = true := by lit_decide

end VG.Proof.Ecdsa.Verify.AArch64.P521
