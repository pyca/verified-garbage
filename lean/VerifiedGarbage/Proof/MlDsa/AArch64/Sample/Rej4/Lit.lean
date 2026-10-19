module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4
materialize_code initCode := (.block (init++setup) : Prog isa)
materialize_code squeezeNeon := (.loop (squeezeStepWith false) (.nonzero .x .x28) : Prog isa)
materialize_code squeezeSha3 := (.loop (squeezeStepWith true) (.nonzero .x .x28) : Prog isa)
materialize_code rejNeon := rejNTT4With false
materialize_code rejSha3 := rejNTT4With true
end VG.Proof.MlDsa.AArch64.Sample.Rej4
