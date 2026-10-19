module

public import VerifiedGarbage.Impl.CmacTripleDes.AArch64
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.CmacTripleDes.AArch64
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.AArch64.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # TDEA-CMAC's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_flat_code Impl.CmacTripleDes.AArch64.init
materialize_flat_code Impl.CmacTripleDes.AArch64.update
materialize_flat_code Impl.CmacTripleDes.AArch64.finalize

end VG
