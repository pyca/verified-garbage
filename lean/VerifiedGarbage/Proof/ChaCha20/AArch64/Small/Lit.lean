module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Small
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Small

@[expose] public section

namespace VG
materialize_code Impl.ChaCha20.AArch64.Small.xor
end VG
