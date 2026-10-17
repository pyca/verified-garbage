module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sha256.X86.ShaNi
meta import VerifiedGarbage.Impl.Sha256.X86.ShaNi
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG
materialize_code Impl.Sha256.X86.ShaNi.compress
end VG
