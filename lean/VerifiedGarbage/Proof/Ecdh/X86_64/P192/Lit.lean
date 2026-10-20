module

public import VerifiedGarbage.Impl.Ecdh.P192.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdh.P192.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P192

open VG.Impl.Ecdh.X86_64

materialize_code exchangeP192

end VG.Proof.Ecdh.X86_64.P192
