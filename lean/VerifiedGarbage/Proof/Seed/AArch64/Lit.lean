module

public import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # The code as literals, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Seed.AArch64

materialize_value g16
materialize_code encrypt
materialize_code decrypt
materialize_code expandKey

end VG.Impl.Seed.AArch64
