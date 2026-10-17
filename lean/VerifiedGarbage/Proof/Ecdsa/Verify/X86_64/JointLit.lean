module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256Adx
end VG
