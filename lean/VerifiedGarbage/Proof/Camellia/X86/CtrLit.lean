module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Camellia.X86.Ctr
meta import VerifiedGarbage.Impl.Camellia.X86.Ctr
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # Camellia-CTR on x86: code literals for the whole-function checks -/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code ctrCode := Impl.Camellia.X86.ctr

end VG.Proof.Camellia.X86
