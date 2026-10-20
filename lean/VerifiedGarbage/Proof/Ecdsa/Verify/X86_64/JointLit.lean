module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256Adx
end VG
