module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.TaintSum
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# Summaries for the residue analysis (x86-64)

`taint_decide` has the kernel analyse the body of a function at every call
of it, in every theorem: the four members of the SHA-512 family call the
same `update` and run the same code after HMAC's `init` calls their `init`,
and each analysis of their HMAC's `init` analysed it again. A summary
(`Taint.SumOk`, `Proof/Framework/TaintSum.lean`) is the analysis of some
code proven once, which `Taint.checkSum` uses in place of the analysis of
the code wherever it applies: a call of the same name, or the same code.

`TaintSum` needs the analysis to be monotone along an order `R`. The
residue analysis (`rtaint`) is not, along any order that compares what is
public, so `R` here is equality (`same`), as `TaintSum` allows (the finest
order):

* a new frame's public bytes are slots of at most 16 bytes cut from the
  bytes of the window outside `sec` (`newSlots`): with fewer secret bytes,
  the frame starts with other slots, not more of them, and a store drops a
  whole slot (`storeStep`), so the frame can end up with less public;
* a freed frame's bytes outside its public slots join `sec` (`popF`): with
  more public slots, `sec` differs, and so does the next frame there.

A frame freed and then allocated again thus breaks any order finer than
equality on `sec` and the frames' slots, which every step can change. With
equality, summaries have no frame (`Fr` holds of anything, `join` keeps its
left side): a summary applies where the taint is exactly its `pre`, and the
analysis goes on from its `post`. The hints get there by weakening (`le`)
the taint to `pre` at the `seq` before the code (`hintW`, `findPre`); with
the same weakening of their hints (e.g. `initHintWeak`), the members of a
family reach the shared code with the same taint.

`rtaint_site%` computes the taint at code a summary is for (its `pre`),
`rtaint_summary` proves a summary, and `rtaint_decide_sum` and
`rtaint_decide_sum_weak` prove an analysis with summaries, all with the
same hints (`hintW`).
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.Taint (Summary SHint)

/-! ## The order: equality -/

/-- Equality of taints, for the kernel. -/
def same (τ σ : FT) : Bool := decide (τ = σ)

theorem same_eq {τ σ : FT} (h : same τ σ = true) : τ = σ := of_decide_eq_true h

theorem same_self (τ : FT) : same τ τ = true := decide_eq_true rfl

/-- The residue analysis is monotone along equality, with no frames. -/
instance : VG.Taint.Frame rtaint where
  R := same
  R_trans h₁ h₂ := by rw [same_eq h₁]; exact h₂
  R_right _ := same_self _
  le_R hm h := by rw [← same_eq h]; exact hm
  step _ h hs := ⟨_, by rw [← same_eq h]; exact hs, same_self _⟩
  condPub _ h hc := by rw [← same_eq h]; exact hc
  meet h₁ h₂ := by rw [same_eq h₁, same_eq h₂]; exact same_self _
  call h hc := ⟨_, by rw [← same_eq h]; exact hc, same_self _⟩
  ret h hc := ⟨_, by rw [← same_eq h]; exact hc, same_self _⟩
  push _ h hc := ⟨_, by rw [← same_eq h]; exact hc, same_self _⟩
  pop _ h hc := ⟨_, by rw [← same_eq h]; exact hc, same_self _⟩
  join a _ := a
  bot := none'
  frameOf a _ := a
  Fr _ _ := true
  Fr_trans _ _ := rfl
  Fr_R _ _ := rfl
  join_hint hm _ := ⟨hm, same_self _, rfl⟩
  join_R ha _ := ha
  frame_le_left _ _ := rfl
  frame_le_right _ _ _ := rfl
  frame_mono _ _ := rfl
  le_frame _ _ := rfl
  le_meet _ _ := rfl
  bot_le _ := rfl
  bot_valid := rfl
  keeps _ _ := true
  keepsCall _ := true
  keeps_bot _ := rfl
  keepsCall_bot := rfl
  step_keeps _ _ _ _ _ := rfl
  call_keeps _ _ _ _ := rfl
  ret_keeps _ _ _ _ := rfl
  push_keeps _ _ _ _ _ := rfl
  pop_keeps _ _ _ _ _ := rfl

/-- A successful `checkSum`, with summaries that hold, used for their code
(`fill`), is a successful `check` that ends with the same taint. -/
theorem any_of_checkSum {S : List (Summary isa FT)} (hS : VG.Taint.AllOk rtaint S) {τ : FT}
    {c : Prog isa} {hc : SHint FT} {p : FT → Bool}
    (h : (VG.Taint.checkSum rtaint S τ c hc).any p = true) (hf : VG.Taint.fill S c hc = c) :
    ∃ g : VG.Taint.Hint FT, (VG.Taint.check rtaint τ c g).any p = true := by
  obtain ⟨τ', e, hp⟩ : ∃ τ', VG.Taint.checkSum rtaint S τ c hc = some τ' ∧ p τ' = true := by
    cases e : VG.Taint.checkSum rtaint S τ c hc with
    | none => rw [e] at h; cases h
    | some τ' => rw [e] at h; exact ⟨τ', rfl, h⟩
  obtain ⟨g, σ', hg, hR, -⟩ := VG.Taint.checkSum_frame (A := rtaint) (F := VG.Taint.Frame.bot (A := rtaint))
    (Φ := VG.Taint.Frame.bot (A := rtaint)) hS rfl e hf VG.Taint.keepsSum_bot (same_self τ) rfl
  refine ⟨g, ?_⟩
  rw [hg, ← same_eq hR]
  exact hp

/-- `RScrub.Analysed.ok`, from the analysis ending as `RScrub.resOkF` says,
for a proof of the existence of a hint (`rtaint_decide_sum`). -/
theorem ok_of_resOkF {sig : Sig} {stack : Nat} {pubs : List (Nat × Nat × Nat)} {code : Prog isa}
    {ks : List Nat}
    (h : ∃ g : VG.Taint.Hint FT,
      (VG.Taint.check rtaint (RScrub.init sig stack pubs) code g).any (RScrub.resOkF · stack ks (Impl.Scrub.X86_64.chunks stack)) = true) :
    ∃ g : VG.Taint.Hint FT,
      (VG.Taint.check rtaint (RScrub.init sig stack pubs) code g).any (RScrub.resOkB · stack ks (Impl.Scrub.X86_64.chunks stack)) = true :=
  let ⟨g, hg⟩ := h
  ⟨g, RScrub.any_resOkB hg⟩

/-! ## Hints

Nothing here needs to be sound: `checkSum` and `fill` check the hint. -/

/-- Whether the summary of code `s` is meant for the code `c`: a call of
the same name, or the same code. -/
def sumFor (s c : Prog isa) : Bool :=
  match s, c with
  | .call n _, .call n' _ => n == n'
  | .call .., _ => false
  | _, _ => VG.Taint.codeBeq s c

/-- The index and `post` of the first summary for `c` whose `pre` is `τ`. -/
def findEq (c : Prog isa) (τ : FT) : List (Summary isa FT) → Nat → Option (Nat × FT)
  | [], _ => none
  | (s, pre, post, _) :: S, k =>
    if sumFor s c && pre == τ then some (k, post) else findEq c τ S (k + 1)

/-- The code that `c` starts with: `c`, and what the first part of `c`
starts with, if `c` is a `seq`. -/
def entries : Prog isa → List (Prog isa)
  | .seq a b => .seq a b :: entries a
  | c => [c]

/-- The `pre` of a summary for code that `c` starts with: one that is `τ`,
or else the first that is at most `τ`. -/
def findPre (c : Prog isa) (τ : FT) (S : List (Summary isa FT)) : Option FT :=
  let es := entries c
  let pres := S.filterMap fun (s, pre, _) => if es.any (sumFor s) then some pre else none
  if pres.contains τ then some τ else pres.find? (le · τ)

/-- The analysis after every `chunk` instructions of `is` but the last,
each weakened by `w`, the analysis going on from it. -/
def chunkMids (w : FT → FT) : FT → List Instr → Nat → List FT
  | _, _, 0 => []
  | τ, is, n + 1 =>
    if is.length ≤ VG.Taint.chunk then [] else
    match rtaint.checkBlock τ (is.take VG.Taint.chunk) with
    | some τ' => let m := w τ'; m :: chunkMids w m (is.drop VG.Taint.chunk) n
    | none => []

/-- The analysis of `c` from `τ`, with its hint (for `checkSum` with the
summaries `S`) and the taint on entry to each part of the code that `probe`
picks, in order. Each taint of the hint is weakened by `w`, or, before code
that a summary is for, to its `pre` (`findPre`); code whose taint is the
`pre` of a summary for it uses it (`findEq`). -/
def hintW (w : FT → FT) (S : List (Summary isa FT)) (probe : Prog isa → Bool) :
    FT → Prog isa → Option (FT × SHint FT × List FT)
  | τ, c => match findEq c τ S 0 with
    | some (k, post) => some (post, .sum k, if probe c then [τ] else [])
    | none => (go τ c).map fun (τ', h, l) => (τ', h, if probe c then τ :: l else l)
where
  go : FT → Prog isa → Option (FT × SHint FT × List FT)
  | τ, .block is =>
    let ms := chunkMids w τ is is.length
    (VG.Taint.checkChunks rtaint VG.Taint.chunk τ is ms).map fun τ' => (τ', .block ms, [])
  | τ, .seq c₁ c₂ =>
    (hintW w S probe τ c₁).bind fun (τ₁, h₁, l₁) =>
      let m := (findPre c₂ (w τ₁) S).getD (w τ₁)
      if le m τ₁ then
        (hintW w S probe m c₂).map fun (τ₂, h₂, l₂) => (τ₂, .seq m h₁ h₂, l₁ ++ l₂)
      else none
  | τ, .ite _ t e =>
    (hintW w S probe τ t).bind fun (τ₁, h₁, l₁) => (hintW w S probe τ e).map fun (τ₂, h₂, l₂) =>
      (meet τ₁ τ₂, .ite h₁ h₂, l₁ ++ l₂)
  | τ, .loop body c => loop c (hintW w S probe · body) VG.Taint.loopFuel (w τ)
  | τ, .call _ body =>
    (callF τ).bind fun τ₁ => (hintW w S probe τ₁ body).bind fun (τ₂, h, l) =>
      (retF τ₂).map fun τ₃ => (τ₃, .call h, l)
  | τ, .frame i body j =>
    (pushF τ i).bind fun τ₁ => (hintW w S probe τ₁ body).bind fun (τ₂, h, l) =>
      (popF τ₂ j).map fun τ₃ => (τ₃, .frame h, l)
  | _, .icall .. => none
  loop (c : Cond) (body : FT → Option (FT × SHint FT × List FT)) :
      Nat → FT → Option (FT × SHint FT × List FT)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h, l) =>
      if le σ σ' && (σ'.ok && σ'.t.flags) then some (σ', .loop σ h, l)
      else loop c body n (w (meet σ σ'))

/-- `hintW`'s taint at the end and hint, as an expression (`τ` and any hint,
if the analysis fails). -/
@[nospecialize] def hintWExpr (w : FT → FT) (S : List (Summary isa FT)) (τ : FT) (c : Prog isa) :
    Lean.Expr :=
  let (τ', h, _) := (hintW w S (fun _ => false) τ c).getD (τ, .block [], [])
  Lean.toExpr (τ', h)

/-- The taint on entry to the `k`-th part of `c` that a summary of `s`
would be for (`sumFor`), in `hintW`'s analysis of `c` from `τ`, if there is
one. -/
@[nospecialize] def siteW (w : FT → FT) (S : List (Summary isa FT)) (τ : FT) (c s : Prog isa)
    (k : Nat) : Option FT :=
  (hintW w S (sumFor s) τ c).bind fun (_, _, l) => l[k]?

end VG.X86_64.RTaint

namespace VG.X86_64.RTaintSum

open Lean Meta Elab Term Tactic

/-- The summaries `ls` (theorems `Taint.SumOk rtaint s`): their list and its proof. -/
meta def sums (ls : Array Ident) : TermElabM (Expr × Expr) := do
  let names ← ls.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  TaintSum.summaries (Lean.mkConst ``VG.X86_64.isa) (Lean.mkConst ``VG.X86_64.RTaint.rtaint) names

/-- `hintW w S τ c`, in compiled code: the taint at the end and the hint. -/
meta def hintOf (w S τ c : Expr) : MetaM (Expr × Expr) := do
  let e := mkAppN (Lean.mkConst ``VG.X86_64.RTaint.hintWExpr) #[w, S, τ, c]
  let r ← unsafe evalExpr Expr (Lean.mkConst ``Expr) e
  unless r.isAppOfArity ``Prod.mk 4 do throwError "rtaint summaries: unexpected {r}"
  return (r.getArg! 2, r.getArg! 3)

/-- Fails if one of the summaries `ls` applies nowhere in the hint `h`: its
`pre` is not the taint at any code it is for, which would otherwise only
cost time. -/
meta def checkAllUsed (who : String) (ls : Array Ident) (h : Expr) : MetaM Unit := do
  let used := TaintSum.usedSums h ls.size
  for k in [0:ls.size] do
    unless used.contains k do
      throwError "{who}: the summary `{ls[k]!}` applies nowhere: its `pre` is not the taint at any \
        code it is for"

/-- The weakening of the hints: `w`, or none. -/
meta def weakOf (w : Option Term) : TermElabM Expr := do
  let ft := Lean.mkConst ``VG.X86_64.RTaint.FT
  match w with
  | some w =>
    let e ← elabTermEnsuringType w (← mkArrow ft ft)
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | none => return .lam `τ ft (.bvar 0) .default

end VG.X86_64.RTaintSum

open Lean Meta Elab Term in
/-- `rtaint_site% w τ c s k using l₁ …`: the taint on entry to the `k`-th
(from 0) call of the same name as `s` (if `s` is a call) or code equal to
`s` in the residue analysis of `c` from `τ` with the hints that
`rtaint_decide_sum_weak w [l₁, …]` gives it (`RTaint.hintW`), as a literal:
the `pre` of a summary of `s`. -/
syntax "rtaint_site% " term:max term:max term:max term:max term:max (" using " ident+)? : term

open Lean Meta Elab Term VG.X86_64.RTaintSum in
elab_rules : term
  | `(rtaint_site% $w $τ $c $s $k $[using $ls*]?) => do
    let w ← weakOf (some w)
    let τ ← elabTermEnsuringType τ (Lean.mkConst ``VG.X86_64.RTaint.FT)
    let c ← elabTermEnsuringType c (mkApp (Lean.mkConst ``VG.Prog) (Lean.mkConst ``VG.X86_64.isa))
    let s ← elabTermEnsuringType s (mkApp (Lean.mkConst ``VG.Prog) (Lean.mkConst ``VG.X86_64.isa))
    let k ← elabTermEnsuringType k (Lean.mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
    let (S, _) ← sums (ls.getD #[])
    let e := mkAppN (Lean.mkConst ``VG.X86_64.RTaint.siteW) #[w, S, ← instantiateMVars τ,
      ← instantiateMVars c, ← instantiateMVars s, ← instantiateMVars k]
    let ty := mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``VG.X86_64.RTaint.FT)
    let some v ← unsafe evalExpr (Option VG.X86_64.RTaint.FT) ty e
      | throwError "rtaint_site%: the analysis fails, or does not reach such code that often"
    return toExpr v

open Lean Meta Elab Term VG.X86_64.RTaintSum in
/-- The theorem `N : Taint.SumOk rtaint (c, pre, post, Frame.bot)` of `rtaint_summary`. -/
meta def VG.X86_64.RTaintSum.summaryCmd (id : Ident) (w : Option Term) (pre c : Term) (ls : Array Ident) :
    TermElabM Unit := do
  let M := Lean.mkConst ``VG.X86_64.isa
  let A := Lean.mkConst ``VG.X86_64.RTaint.rtaint
  let w ← weakOf w
  let pre ← elabTermEnsuringType pre (Lean.mkConst ``VG.X86_64.RTaint.FT)
  let c ← elabTermEnsuringType c (mkApp (Lean.mkConst ``VG.Prog) M)
  synthesizeSyntheticMVarsNoPostponing
  let pre ← instantiateMVars pre
  let c ← instantiateMVars c
  if pre.hasMVar || c.hasMVar then throwError "rtaint_summary: the taint and the code must be closed"
  let (S, hS) ← sums ls
  let (post, hint) ← hintOf w S pre c
  checkAllUsed "rtaint_summary" ls hint
  let fr ← synthInstance (mkApp2 (Lean.mkConst ``VG.Taint.Frame) M A)
  let F := mkApp3 (Lean.mkConst ``VG.Taint.Frame.bot) M A fr
  let s ← mkAppM ``Prod.mk #[c, ← mkAppM ``Prod.mk #[pre, ← mkAppM ``Prod.mk #[post, F]]]
  let ty := mkApp4 (Lean.mkConst ``VG.Taint.SumOk) M A fr s
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let gs ← Tactic.run mv.mvarId! (TaintSum.proveWith M A S hS c ``VG.Taint.sumOk_of_checkSum
    #[pre, post, F] hint)
  unless gs.isEmpty do throwError "rtaint_summary: goals remain"
  let v ← instantiateMVars mv
  addDecl <| .thmDecl
    { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := ty, value := v }

/-- `rtaint_summary N : w pre code using l₁ …` proves the summary
`N : Taint.SumOk rtaint (code, pre, post, Frame.bot)` of the residue
analysis, with `post` what the analysis of `code` from `pre` ends with, by
evaluation (`lit_decide`), with the hints of `RTaint.hintW` (weakened by
`w`, `id` if `_`) and the summaries `lᵢ` in place of the calls they apply to. -/
syntax "rtaint_summary " ident " : " term:max term:max term:max (" using " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(rtaint_summary $id : $w $pre $c $[using $ls*]?) =>
    liftTermElabM (VG.X86_64.RTaintSum.summaryCmd id (if w.raw.isOfKind ``Lean.Parser.Term.hole then none else some w) pre c (ls.getD #[]))

open Lean Meta Elab Tactic Term VG.X86_64.RTaintSum in
/-- `rtaint_decide_sum` and `rtaint_decide_sum_weak`. -/
meta def VG.X86_64.RTaintSum.decideSum (who : String) (w : Option Term) (ls : Array Ident) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← whnfD (← instantiateMVars (← g.getType))
  let bad := m!"{who}: the goal is not `∃ g, (Taint.check rtaint τ c g).any p = true`"
  let some (_, body) := ty.app2? ``Exists | throwError bad
  let .lam _ _ b _ := body | throwError bad
  let some (_, lhs, _) := b.eq? | throwError bad
  unless lhs.isAppOfArity ``Option.any 3 do throwError bad
  let p := lhs.getArg! 1
  let chk := lhs.getArg! 2
  unless chk.isAppOfArity ``VG.Taint.check 5 && !p.hasLooseBVars do throwError bad
  let (τ, c) := (chk.getArg! 2, chk.getArg! 3)
  let w ← weakOf w
  let (S, hS) ← sums ls
  let (_, hint) ← hintOf w S τ c
  checkAllUsed who ls hint
  let e ← mkAppOptM ``VG.X86_64.RTaint.any_of_checkSum
    #[some S, some hS, some τ, some c, some hint, some p]
  let (mvs, _, _) ← forallMetaTelescope (← inferType e)
  let pf := mkAppN e mvs
  unless ← isDefEq (← inferType pf) ty do
    throwError "{who}: {← inferType pf} does not match the goal {ty}"
  g.assign pf
  let m₁ :: m₂ :: _ := mvs.toList | throwError "{who}: unexpected arguments"
  setGoals [m₁.mvarId!]
  evalTactic (← `(tactic| lit_decide))
  setGoals [m₂.mvarId!]
  TaintSum.fillRfl

/-- `rtaint_decide_sum [l₁, …]` proves
`∃ g, (Taint.check rtaint τ c g).any p = true` with the summaries `lᵢ`
(`rtaint_summary`) in place of the calls they apply to, and the hints of
`RTaint.hintW`, by evaluation (`lit_decide`). -/
elab "rtaint_decide_sum " "[" ls:ident,* "]" : tactic =>
  VG.X86_64.RTaintSum.decideSum "rtaint_decide_sum" none ls.getElems

/-- `rtaint_decide_sum`, with the taints of the hints weakened by
`w : FT → FT` (as `taint_decide_weak`). -/
elab "rtaint_decide_sum_weak " w:term:max " [" ls:ident,* "]" : tactic =>
  VG.X86_64.RTaintSum.decideSum "rtaint_decide_sum_weak" (some w) ls.getElems
