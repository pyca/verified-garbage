module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Ecdsa.AArch64

theorem verify_abi : abiK verifyP521 = true := by lit_decide

end VG.Proof.Ecdsa.Verify.AArch64.P521
