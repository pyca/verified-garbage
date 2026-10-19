module

public meta import Lean.Meta.Reduce
public import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.TCB.Arm.Target
import Lean.Meta.Reduce
import VerifiedGarbage.TCB.Arm.Target

/-!
# Moving a proof to a shared contract, on Arm

`contract_implies` unfolds `Arm.classify` on the signature's argument widths.
Unfolded by `dsimp`, every recursive call is duplicated (its result is used
twice), so a signature of a few words costs hundreds of unfoldings, once per
field of `Contract.Implies`. `reduceClassify` evaluates it in one step instead;
pass it in place of `Arm.classify`.
-/

public meta section

namespace VG.Arm

open Lean Meta in
/-- Evaluates `Arm.classify` (by definitional unfolding, so the result needs no proof). -/
dsimproc reduceClassify (classify _ _ _) := fun e => do
  return .done (← withTransparency .all <| Meta.reduce e (skipTypes := true) (skipProofs := true))

end VG.Arm
