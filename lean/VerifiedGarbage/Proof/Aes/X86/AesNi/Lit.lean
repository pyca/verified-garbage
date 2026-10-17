module

public import VerifiedGarbage.Impl.Aes.X86.AesNi
meta import VerifiedGarbage.Impl.Aes.X86.AesNi
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Impl.Aes.X86.AesNi
materialize_code expandKey
materialize_code ctr32
end VG.Impl.Aes.X86.AesNi
