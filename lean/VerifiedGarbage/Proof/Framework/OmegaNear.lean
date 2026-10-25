module

public import VerifiedGarbage.Proof.Framework.Omega
public meta import VerifiedGarbage.Proof.Framework.Omega
public meta import Lean.Elab.Tactic.Basic

/-!
# `omega_arith` on the nearest facts first

Untrusted: this only changes how proofs are found.

The kernel checks every `omega` certificate, at tens of milliseconds even
for a few facts (`Lean.Omega`'s coefficient lists, normalized by
evaluation), and more for every fact and atom in it. `omega_arith` gives
`omega` every arithmetic fact connected to the goal (`relevantFacts`): deep
in a proof about a workspace's offsets, that is most of the context, since
the offsets all share atoms (the sizes, the base). `omega_near` tries
smaller problems first, then does what `omega_arith` does:

* a goal without free variables (a side condition about literal offsets), by
  `decide`;
* the facts sharing an atom with the goal (`relevantFactsDepth … 1`), then
  those within two steps of it;
* `omega_arith`.

A failed attempt on a few facts costs `omega` little, against the kernel's
check of a large certificate when one succeeds.
-/

public meta section

namespace VG.Omega

open Lean Meta Elab Tactic

/-- `relevantFacts`, taking facts in at most `depth` rounds from the goal. -/
def relevantFactsDepth (hs : Array Expr) (goal : Expr) (depth : Nat) : MetaM (Array Expr) := do
  let mut seen ← atoms goal {}
  if seen.isEmpty then return #[]
  let mut infos : Array (Std.HashSet Expr × Option Expr) := #[]
  for h in hs do
    let ty ← inferType h
    infos := infos.push (← atoms ty {}, ← definedAtom? ty)
  let mut taken := Array.replicate hs.size false
  for _ in [0:depth] do
    let seen0 := seen
    let mut changed := false
    for i in [:infos.size] do
      if taken[i]! then continue
      let (as, d) := infos[i]!
      if match d with | some x => seen0.contains x | none => as.any seen0.contains then
        taken := taken.set! i true
        seen := as.fold (·.insert ·) seen
        changed := true
    if !changed then break
  return (hs.zip taken).filterMap fun (h, t) => if t then some h else none

/-- `decide` on a closed goal, `omega` on the facts within one, then two,
rounds of the goal, then `omegaArith`. -/
def omegaNear : TacticM Unit := do
  let t ← instantiateMVars (← getMainTarget)
  if !t.hasFVar && !t.hasMVar then
    let saved ← saveState
    try
      evalTactic (← `(tactic| decide))
      return
    catch _ => saved.restore
  let stages ← withMainContext do
    let all ← (← getLocalHyps).filterM fun h => do isArithProp (← inferType h)
    let goal ← getMainTarget
    let full ← relevantFacts all goal
    let mut st : Array (Array Expr) := #[]
    for d in [1, 2] do
      let f ← relevantFactsDepth all goal d
      if f.size < full.size && st.all (·.size < f.size) then st := st.push f
    pure st
  for f in stages do
    let saved ← saveState
    try
      omegaFromFacts f (exactTypeOnly := true)
      return
    catch _ => saved.restore
  omegaArith

end VG.Omega

/-- `omega_arith`, trying smaller problems first (see the module doc). -/
elab "omega_near" : tactic => VG.Omega.omegaNear
