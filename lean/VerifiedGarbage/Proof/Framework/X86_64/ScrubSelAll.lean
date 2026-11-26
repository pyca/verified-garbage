module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public meta import Lean.Elab.Tactic.Basic
import VerifiedGarbage.Proof.Framework.TaintBatch
public meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# Several residue analyses in one kernel evaluation (x86-64)

A cipher's modes run the same code from the same taint, and the kernel
forgets what it evaluated at the end of a declaration: `taint_decide_sels`
proves what `verifiedScrubbedSel` needs of several functions (`SelResidue`)
in one, from which each function takes its own (`residue`,
`Proof/Camellia/X86_64/Scrub.lean`), as `taint_decide_ct_all` does for the
other targets' analyses.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- The residue analysis of `code`, of signature `sig`, with `n` bytes of
stack and the bytes `pubs` of its buffers public, succeeds, for some hint,
where the runs `rs` of granules are wiped. -/
abbrev SelResidue (sig : Sig) (n : Nat) (pubs : List (Nat × Nat × Nat)) (rs : List (Nat × Nat))
    (code : Prog isa) : Prop :=
  ∃ h, (VG.Taint.check RTaint.rtaint (RScrub.init sig n pubs) code h).any
    (RScrub.resOkF · n (runKs rs) (chunksA n)) = true

open Lean Meta in
/-- The goals of `g`, a conjunction: those that are `∃ h, …` of a hint. -/
private meta partial def splitGoals (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty ← whnfR (← g.getType)
  if let some (a, b) := ty.and? then
    let x ← mkFreshExprSyntheticOpaqueMVar a
    let y ← mkFreshExprSyntheticOpaqueMVar b
    g.assign (mkApp4 (mkConst ``And.intro) a b x y)
    return (← splitGoals x.mvarId!) ++ (← splitGoals y.mvarId!)
  if ty.isAppOfArity ``Exists 2 then
    let (α, p) := (ty.appFn!.appArg!, ty.appArg!)
    let w ← mkFreshExprSyntheticOpaqueMVar α
    let x ← mkFreshExprSyntheticOpaqueMVar (p.beta #[w])
    g.assign (mkApp4 (mkConst ``Exists.intro ty.getAppFn.constLevels!) α p w x)
    return [x.mvarId!]
  return [g]

open Lean Elab Tactic in
/-- Proves a conjunction of `SelResidue`s in one kernel evaluation. -/
elab "taint_decide_sels" : tactic => do
  let g ← getMainGoal
  replaceMainGoal (← splitGoals g)
  evalTactic (← `(tactic| taint_decide_all))

end VG.X86_64.Scrub
