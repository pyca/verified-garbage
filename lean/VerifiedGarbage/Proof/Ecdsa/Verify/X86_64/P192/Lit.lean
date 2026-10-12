module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P192.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P192Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P192

open VG.Impl.Ecdsa.Verify.X86_64

materialize_code verifyP192

end VG.Proof.Ecdsa.Verify.X86_64.P192
