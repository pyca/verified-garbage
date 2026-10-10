import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# Constant-time checks proved once for every callee

A caller `G x` of functions that depend on a parameter `x` (e.g. the
permutation and the sponge's functions of a Keccak backend) is checked with
summaries of those calls (`taint_decide_sum`). `checkSum` looks neither at
the code of a summarized call nor at the names of calls, so when the
summaries' `pre`, `post` and frame do not depend on `x`, the same hint is
checked for every `x` at once: `taint_decide_generic` proves
`∃ h, (A.check τ (G x) h).isSome = true` for a variable `x`, from summaries
`hS : Taint.AllOk A (S x)` of the calls of `G x`, with the hint computed for
a representative `x := rep`. The kernel evaluates `checkSum` and `fill` with
`x` a variable, unfolding `G x` only down to the summarized calls.

Each instance then needs only its summaries (`S x` for its `x`), which may
end with more public than `S`'s: `SumOk.weaken` gives them `S`'s `post`.
-/

namespace VG.Taint

variable {M : ISA} {A : Taint M}

/-- The summary that a theorem `SumOk A s` is about. -/
abbrev sumOf [Frame A] {s : Summary M A.T} (_ : SumOk A s) : Summary M A.T := s

/-- A summary holds with any `post` that has less public (`R`). -/
theorem SumOk.weaken [hm : Frame A] {c : Prog M} {pre post post' F : A.T}
    (h : SumOk A (c, pre, post, F)) (hp : Mono.R (A := A) post' post = true) :
    SumOk A (c, pre, post', F) := fun τ hτ => by
  obtain ⟨g, τ', hg, hpost, hfr⟩ := h τ hτ
  exact ⟨g, τ', hg, hm.R_trans hp hpost, hfr⟩

/-- A summary with a frame gives one from a taint with more public (`pre'`),
which ends with what the summary and its frame give there (as `checkSum`
does where it uses the summary), with no frame. -/
theorem SumOk.restrict [hm : Frame A] {c : Prog M} {pre post F pre' post' : A.T}
    (h : SumOk A (c, pre, post, F)) (hpre : Mono.R (A := A) pre pre' = true)
    (hpost : Mono.R (A := A) post' (Frame.join post (Frame.frameOf pre' F)) = true) :
    SumOk A (c, pre', post', Frame.bot) := fun τ hτ => by
  obtain ⟨g, τ', hg, hp, hfr⟩ := h τ (hm.R_trans hpre hτ)
  have hj := hm.join_R hp (hm.Fr_trans (hm.frame_mono F hτ) hfr)
  exact ⟨g, τ', hg, hm.R_trans hpost hj,
    hm.Fr_trans (hm.frame_le_right τ hm.bot_valid) (hm.bot_le (hm.R_right hp))⟩

end VG.Taint

namespace VG.TaintSum

open Lean Meta Elab Tactic

/-- `taint_decide_generic x := rep using hS` proves the main goal
`∃ h, (A.check τ c h).isSome = true`, where `c` and the summaries of
`hS : Taint.AllOk A S` may depend on the local `x`: by `checkSum` and `fill`,
with the hint of `c` and `S` for `x := rep`, which the kernel alone checks
for any `x` (`Taint.exists_check_of_checkSum`). -/
elab "taint_decide_generic " x:ident " := " rep:term " using " hs:ident : tactic =>
  withMainContext do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let err := "taint_decide_generic: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
    let some (_, body) := ty.app2? ``Exists | throwError err
    let .lam _ _ b _ := body | throwError err
    let some chk := b.find? (·.isAppOfArity ``Taint.check 5) | throwError err
    let args := chk.getAppArgs
    let (M, A, τ, c) := (args[0]!, args[1]!, args[2]!, args[3]!)
    let xv ← getFVarFromUserName x.getId
    let hS ← getFVarFromUserName hs.getId
    let hSty ← instantiateMVars (← inferType hS)
    unless hSty.isAppOfArity ``Taint.AllOk 4 do
      throwError "taint_decide_generic: {hs} is not a `Taint.AllOk`: {hSty}"
    let S := hSty.getArg! 3
    let r ← Term.elabTermEnsuringType rep (← inferType xv)
    Term.synthesizeSyntheticMVarsNoPostponing
    let r ← instantiateMVars r
    let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
    -- The hint, for `x := rep`, in compiled code; the kernel checks it for any `x`.
    let (_, hint) ← hintChecked "taint_decide_generic" M A fr (S.replaceFVar xv r) τ
      (c.replaceFVar xv r)
    let isSome ← mkAppM ``Option.isSome
      #[mkAppN (mkConst ``Taint.checkSum) #[M, A, fr, S, τ, c, hint]]
    let hc ← mkAuxTheorem (← mkEq isSome (mkConst ``Bool.true))
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    let T := mkApp2 (mkConst ``Taint.T) M A
    let fl := mkAppN (mkConst ``Taint.fill) #[M, T, S, c, hint]
    let hf ← mkAuxTheorem (← mkEq fl c) (← mkEqRefl c)
    let pf ← mkAppOptM ``Taint.exists_check_of_checkSum #[M, A, fr, S, hS, c, τ, hint, hc, hf]
    let (mvs, _, _) ← forallMetaTelescope (← inferType pf)
    let pf := mkAppN pf mvs
    unless ← isDefEq (← inferType pf) ty do
      throwError "taint_decide_generic: {← inferType pf} does not match the goal {ty}"
    g.assign pf
    -- `R τ τ`: the taint on entry satisfies the domain's invariant.
    for m in mvs do
      unless ← m.mvarId!.isAssigned do
        setGoals [m.mvarId!]
        evalTactic (← `(tactic| decide +kernel))
    setGoals []

end VG.TaintSum

namespace VG.Taint

variable {M : ISA} {A : Taint M}

theorem AllOk.nil [Frame A] : AllOk A ([] : List (Summary M A.T)) := trivial

theorem AllOk.cons [Frame A] {s : Summary M A.T} {S : List (Summary M A.T)} (h : SumOk A s)
    (t : AllOk A S) : AllOk A (s :: S) := ⟨h, t⟩

theorem AllOk.append [Frame A] {S S' : List (Summary M A.T)} (h : AllOk A S) (h' : AllOk A S') :
    AllOk A (S ++ S') := by
  induction S with
  | nil => exact h'
  | cons s S ih => exact ⟨h.1, ih h.2⟩

end VG.Taint
