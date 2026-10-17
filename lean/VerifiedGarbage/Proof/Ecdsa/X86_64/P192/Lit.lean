module

public import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P192

open VG.Impl.Ecdsa.X86_64

materialize_code signP192

end VG.Proof.Ecdsa.X86_64.P192
