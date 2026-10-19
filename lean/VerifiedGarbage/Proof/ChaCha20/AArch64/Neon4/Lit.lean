module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG

/- Cache the kernel-checked four-block stream code for all caller audits. -/
materialize_code Impl.ChaCha20.AArch64.Neon4.xor

end VG
