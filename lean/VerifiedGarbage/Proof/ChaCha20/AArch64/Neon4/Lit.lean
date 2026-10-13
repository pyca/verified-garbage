module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG

/- Cache the kernel-checked four-block stream code for all caller audits. -/
materialize_code Impl.ChaCha20.AArch64.Neon4.xor

end VG
