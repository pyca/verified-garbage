module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG
materialize_code ChaCha20.AArch64.Mixed8.xorNeon := Impl.ChaCha20.AArch64.Mixed8.xor false
materialize_code ChaCha20.AArch64.Mixed8.xorSve2 := Impl.ChaCha20.AArch64.Mixed8.xor true
end VG
