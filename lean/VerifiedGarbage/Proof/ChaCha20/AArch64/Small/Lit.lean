module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Small
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Small
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG
materialize_code ChaCha20.AArch64.Small.shortNeon := Impl.ChaCha20.AArch64.Small.short false
materialize_code ChaCha20.AArch64.Small.xorNeon := Impl.ChaCha20.AArch64.Small.xor false
materialize_code ChaCha20.AArch64.Small.shortSve2 := Impl.ChaCha20.AArch64.Small.short true
materialize_code ChaCha20.AArch64.Small.xorSve2 := Impl.ChaCha20.AArch64.Small.xor true
end VG
