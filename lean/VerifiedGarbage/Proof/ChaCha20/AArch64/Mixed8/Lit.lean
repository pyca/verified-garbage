module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG
materialize_code ChaCha20.AArch64.Mixed8.xorNeon := Impl.ChaCha20.AArch64.Mixed8.xor false
materialize_code ChaCha20.AArch64.Mixed8.xorSve2 := Impl.ChaCha20.AArch64.Mixed8.xor true
end VG
