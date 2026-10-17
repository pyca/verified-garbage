module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6

@[expose] public section

namespace VG
materialize_code Impl.ChaCha20.AArch64.Rows6.xor
end VG
