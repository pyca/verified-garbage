module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P192.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
import VerifiedGarbage.Impl.Ecdh.P192.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P192.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P192

open VG.Impl.Ecdsa.Verify.X86_64

materialize_code verifyP192

end VG.Proof.Ecdsa.Verify.X86_64.P192
