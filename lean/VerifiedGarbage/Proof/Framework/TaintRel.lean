module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.Framework.Taint

/-!
# Summaries of called functions proven relationally

A summary of `TaintSum.lean` holds because the analysis of the function's code
succeeds: it saves checking that code again in every caller, but knows no
more than the analysis. A *relational summary* `(code, pre, post)` instead
says what any proof of the function's constant time gives (`RSum.Ok`): from
two states that agree on what `τ` says is public (`τ` at least `pre`), two
runs of `code` leak the same trace and end agreeing on what `post τ` says is
public. Its proof may use another domain (one that tracks more, say values
spilled to and reloaded from memory or vector registers) and the function's
correctness (that it restores what it saved); its callers use it from the
domain they are checked in, so the summary carries over to every caller.

`checkR` is `Taint.check` with the summaries `S`: at a `sum k` hint, the
`k`-th summary gives `post τ`, whatever the code there. `fillR S c h` is `c`
with each summary's code in place of the code at its `sum` hint; the kernel
proves `fillR S c h = c` by unfolding (`Eq.refl`), which says that each
summary was used for its own code, without comparing code itself.
`RelCT.taintR` turns a successful check into `RelCT`, and `taint_decide_rel`
proves the check, with the hint computed in compiled code.
-/

@[expose] public section

namespace VG.Taint

variable {M : ISA} (A : Taint M)

/-- A hint for `checkR`: a `Hint`, where `sum k` uses the `k`-th summary. -/
inductive RHint (T : Type) where
  | block (mids : List T) (chunkSize : Nat := 256)
  | seq (mid : T) (h₁ h₂ : RHint T)
  | ite (h₁ h₂ : RHint T)
  | loop (inv : T) (h : RHint T)
  | call (h : RHint T)
  | frame (h : RHint T)
  | sum (k : Nat)
  deriving Lean.ToExpr

/-- A relational summary: the code, the least it needs public, and what is
public after it, from what is public before. -/
structure RSum (M : ISA) (T : Type) where
  code : Prog M
  pre : T
  post : T → T

/-- The summary holds: from states that agree on at least `pre`, two runs of
its code leak the same trace and end agreeing on `post τ`. -/
def RSum.Ok (s : RSum M A.T) : Prop :=
  ∀ τ, A.le s.pre τ = true → RelCT M (A.Agree τ) s.code (A.Agree (s.post τ))

/-- Every summary of the list holds. -/
def RAllOk : List (RSum M A.T) → Prop
  | [] => True
  | s :: S => s.Ok A ∧ RAllOk S

/-- `check`, with the summaries `S`. -/
def checkR (S : List (RSum M A.T)) (τ : A.T) (c : Prog M) (h : RHint A.T) : Option A.T :=
  match h, τ, c with
  | .sum k, τ, _ => match S[k]? with
    | some s => if A.le s.pre τ then some (s.post τ) else none
    | none => none
  | .block ms chunkSize, τ, .block is => A.checkChunks chunkSize τ is ms
  | .seq mid h₁ h₂, τ, .seq c₁ c₂ =>
    (checkR S τ c₁ h₁).bind fun τ' => if A.le mid τ' then checkR S mid c₂ h₂ else none
  | .ite h₁ h₂, τ, .ite c t e =>
    if A.condPub τ c then
      (checkR S τ t h₁).bind fun τ₁ => (checkR S τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | .loop σ h, τ, .loop body c =>
    if A.le σ τ then
      (checkR S σ body h).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
    else none
  | .call h, τ, .call _ body => (A.call τ).bind fun τ₁ => (checkR S τ₁ body h).bind A.ret
  | .frame h, τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (checkR S τ₁ body h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none
termination_by structural h

variable {A} in
/-- `c`, with the code of the summary at each `sum k` of the hint in place of
what is there. -/
def fillR {T : Type} (S : List (RSum M T)) (c : Prog M) (h : RHint T) : Prog M :=
  match h, c with
  | .sum k, c => match S[k]? with
    | some s => s.code
    | none => c
  | .seq _ h₁ h₂, .seq a b => .seq (fillR S a h₁) (fillR S b h₂)
  | .ite h₁ h₂, .ite cd t e => .ite cd (fillR S t h₁) (fillR S e h₂)
  | .loop _ h, .loop b cd => .loop (fillR S b h) cd
  | .call h, .call n b => .call n (fillR S b h)
  | .frame h, .frame i b j => .frame i (fillR S b h) j
  | _, c => c
termination_by structural h

/-! ## Soundness -/

variable {A}

theorem RAllOk.get {S : List (RSum M A.T)} (hS : RAllOk A S) {k : Nat} {s : RSum M A.T}
    (h : S[k]? = some s) : s.Ok A := by
  induction S generalizing k with
  | nil => cases h
  | cons s' S ih =>
    cases k with
    | zero => cases h; exact hS.1
    | succ k => exact ih hS.2 h

/-- The loop rule, from the soundness of the body's check. -/
theorem checkR_loop {body : Prog M} {c : M.Cond} {σ σ' : A.T}
    (hb : ∀ {s₁ s₂ t₁ t₂ s₁' s₂'}, A.Agree σ s₁ s₂ → Exec M body s₁ t₁ s₁' → Exec M body s₂ t₂ s₂' →
      t₁ = t₂ ∧ A.Agree σ' s₁' s₂') (hle : A.le σ σ' = true) (hc : A.condPub σ' c = true) :
    ∀ {s₁ s₂ t₁ t₂ s₁' s₂'}, A.Agree σ s₁ s₂ → Exec M (.loop body c) s₁ t₁ s₁' →
      Exec M (.loop body c) s₂ t₂ s₂' → t₁ = t₂ ∧ A.Agree σ' s₁' s₂' := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
  generalize hl : (Code.loop body c : Prog M) = l at e₁
  induction e₁ generalizing s₂ t₂ s₂' with
  | loopExit a hc' =>
    cases hl
    cases e₂ with
    | loopExit a' _ => obtain ⟨rfl, hq⟩ := hb ha a a'; exact ⟨rfl, hq⟩
    | loopNext a' hc'' _ =>
      obtain ⟨_, ha₁⟩ := hb ha a a'
      rw [← A.cond_sound ha₁ hc, hc'] at hc''; cases hc''
  | loopNext a hc' _ _ ih₂ =>
    cases hl
    cases e₂ with
    | loopExit a' hc'' =>
      obtain ⟨_, ha₁⟩ := hb ha a a'
      rw [← A.cond_sound ha₁ hc, hc'] at hc''; cases hc''
    | loopNext a' _ b' =>
      obtain ⟨rfl, ha₁⟩ := hb ha a a'
      obtain ⟨rfl, ha₂⟩ := ih₂ (A.le_sound hle ha₁) b' rfl
      exact ⟨rfl, ha₂⟩
  | _ => cases hl

theorem checkR_sound {S : List (RSum M A.T)} (hS : RAllOk A S) :
    ∀ (h : RHint A.T) {c : Prog M} {τ τ' : A.T} {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak},
      A.checkR S τ c h = some τ' → A.Agree τ s₁ s₂ → Exec M (fillR S c h) s₁ t₁ s₁' →
      Exec M (fillR S c h) s₂ t₂ s₂' → t₁ = t₂ ∧ A.Agree τ' s₁' s₂'
  | .sum k, c, τ, τ', s₁, s₂, s₁', s₂', t₁, t₂, h, ha, e₁, e₂ => by
    unfold checkR at h
    unfold fillR at e₁ e₂
    split at h <;> [skip; cases h]
    rename_i s hk
    simp only [hk] at e₁ e₂
    split at h <;> [rename_i hle; cases h]
    cases h
    exact (hS.get hk) τ hle _ _ _ _ _ _ ha e₁ e₂
  | .block ms chunkSize, c, τ, τ', _, _, _, _, _, _, h, ha, e₁, e₂ => by
    cases c with
    | block is =>
      have h : A.checkChunks chunkSize τ is ms = some τ' := h
      cases e₁ with
      | block h₁ => cases e₂ with
        | block h₂ => exact checkChunks_sound h ha h₁ h₂
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | .seq mid g₁ g₂, c, τ, τ', _, _, _, _, _, _, h, ha, e₁, e₂ => by
    cases c with
    | seq c₁ c₂ =>
      have h : ((A.checkR S τ c₁ g₁).bind fun τ' => if A.le mid τ' then A.checkR S mid c₂ g₂ else none) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hle; cases h₂]
      cases e₁ with
      | seq a b => cases e₂ with
        | seq a' b' =>
          obtain ⟨rfl, ha₁⟩ := checkR_sound hS g₁ h₁ ha a a'
          obtain ⟨rfl, ha₂⟩ := checkR_sound hS g₂ h₂ (A.le_sound hle ha₁) b b'
          exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | .ite g₁ g₂, c, τ, τ', _, _, _, _, _, _, h, ha, e₁, e₂ => by
    cases c with
    | ite cnd t e =>
      have h : (if A.condPub τ cnd then
          (A.checkR S τ t g₁).bind fun τ₁ => (A.checkR S τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, rfl⟩ := h
      cases e₁ with
      | iteT hc' a => cases e₂ with
        | iteT _ b => obtain ⟨rfl, hq⟩ := checkR_sound hS g₁ h₁ ha a b; exact ⟨rfl, A.meet_left hq⟩
        | iteF hc'' _ => rw [← A.cond_sound ha hp, hc'] at hc''; cases hc''
      | iteF hc' a => cases e₂ with
        | iteT hc'' _ => rw [← A.cond_sound ha hp, hc'] at hc''; cases hc''
        | iteF _ b => obtain ⟨rfl, hq⟩ := checkR_sound hS g₂ h₂ ha a b; exact ⟨rfl, A.meet_right hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | .loop σ hb, c, τ, τ', _, _, _, _, _, _, h, ha, e₁, e₂ => by
    cases c with
    | loop body cnd =>
      have h : (if A.le σ τ then
          (A.checkR S σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' cnd then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      exact checkR_loop (fun ha a b => checkR_sound hS hb hb' ha a b) hl.1 hl.2 (A.le_sound hστ ha) e₁ e₂
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | .call g, c, τ, τ', _, _, _, _, _, _, h, ha, e₁, e₂ => by
    cases c with
    | call n body =>
      have h : ((A.call τ).bind fun τ₁ => (A.checkR S τ₁ body g).bind A.ret) = some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₁ with
      | call hc₁ b hr => cases e₂ with
        | call hc₂ b' hr₂ =>
          obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
          obtain ⟨rfl, ha₂⟩ := checkR_sound hS g h₂ ha₁' b b'
          obtain ⟨ha₃, ha₃'⟩ := A.ret_sound ha₂ h₃ hr hr₂
          exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | .frame g, c, τ, τ', _, _, _, _, _, _, h, ha, e₁, e₂ => by
    cases c with
    | frame i body j =>
      have h : ((A.push τ i).bind fun τ₁ => (A.checkR S τ₁ body g).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₁ with
      | frame hp₁ b hq => cases e₂ with
        | frame hp₂ b' hq₂ =>
          obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
          obtain ⟨rfl, ha₂⟩ := checkR_sound hS g h₂ ha₁' b b'
          obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
          exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'

end VG.Taint

namespace VG

namespace RelCT

variable {M : ISA} {A : Taint M}

/-- A successful check with relational summaries proves `RelCT`, ending with
what the check ends with public. -/
theorem taintR_post {S : List (Taint.RSum M A.T)} (hS : Taint.RAllOk A S) {P : M.State → M.State → Prop}
    {c : Prog M} (τ : A.T) (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τ s₁ s₂) {hc : Taint.RHint A.T} {τ' : A.T}
    (hf : Taint.fillR S c hc = c) (h : A.checkR S τ c hc = some τ') : RelCT M P c (A.Agree τ') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [← hf] at e₁ e₂
  exact Taint.checkR_sound hS hc h (hp _ _ hP) e₁ e₂

/-- A successful check with relational summaries proves `RelCT`. -/
theorem taintR {S : List (Taint.RSum M A.T)} (hS : Taint.RAllOk A S) {P : M.State → M.State → Prop}
    {c : Prog M} (τ : A.T) (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τ s₁ s₂) {hc : Taint.RHint A.T}
    (hf : Taint.fillR S c hc = c) (h : (A.checkR S τ c hc).isSome = true) : RelCT M P c fun _ _ => True := by
  obtain ⟨τ', h'⟩ := Option.isSome_iff_exists.mp h
  exact (taintR_post hS τ hp hf h').mono (fun _ _ h => h) fun _ _ _ => trivial

end RelCT

namespace Taint

variable {M : ISA} (A : Taint M)

/-! ## Computing hints

Nothing here needs to be sound: `checkR` checks the hint, and `fillR` that
each summary is used for its code. -/

/-- The first summary of a call of `n` that applies from `τ`: its index and
what is public after it. -/
def findRSum (n : String) (τ : A.T) : List (RSum M A.T) → Nat → Option (Nat × A.T)
  | [], _ => none
  | s :: S, k => match s.code with
    | .call n' _ => if n' == n && A.le s.pre τ then some (k, s.post τ) else findRSum n τ S (k + 1)
    | _ => findRSum n τ S (k + 1)

/-- `hint`, with the first summary that applies at each call (by its name). -/
def hintR (S : List (RSum M A.T)) (chunkSize : Nat) : A.T → Prog M → Option (A.T × RHint A.T)
  | τ, .block is => (A.checkBlock τ is).map fun τ' =>
    (τ', .block (chunkHints A chunkSize τ is is.length) chunkSize)
  | τ, .seq c₁ c₂ =>
    (hintR S chunkSize τ c₁).bind fun (τ₁, h₁) => (hintR S chunkSize τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite _ t e =>
    (hintR S chunkSize τ t).bind fun (τ₁, h₁) => (hintR S chunkSize τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hintR S chunkSize · body) loopFuel τ
  | τ, .call n body => match findRSum A n τ S 0 with
    | some (k, post) => some (post, .sum k)
    | none => (A.call τ).bind fun τ₁ => (hintR S chunkSize τ₁ body).bind fun (τ₂, h) => (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hintR S chunkSize τ₁ body).bind fun (τ₂, h) => (A.pop τ₂ j).map (·, .frame h)
  | _, .icall .. => none
where
  go (c : M.Cond) (body : A.T → Option (A.T × RHint A.T)) : Nat → A.T → Option (A.T × RHint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- The hint for `c` from `τ` (any hint, if the analysis fails). -/
@[nospecialize] def hintROf (S : List (RSum M A.T)) (chunkSize : Nat) (τ : A.T) (c : Prog M) : RHint A.T :=
  ((hintR A S chunkSize τ c).map (·.2)).getD (.block [] chunkSize)

/-- `toExpr` of a hint, compiled once here. -/
@[nospecialize] def RHint.toExprNS {T : Type} [Lean.ToExpr T] (h : RHint T) : Lean.Expr :=
  Lean.toExpr h

end Taint

open Lean Meta Elab Tactic in
/-- `taint_decide_rel` at one interval. -/
meta def taintDecideRelAt (chunkSize : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "taint_decide_rel: the goal is not an equation about `Taint.checkR A S τ c h`"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.checkR 6)
    | throwError "taint_decide_rel: the goal is not an equation about `Taint.checkR A S τ c h`"
  let args := chk.getAppArgs
  let (m, a, S, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!)
  let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
  let hint := mkApp6 (mkConst ``Taint.hintROf) m a S chunkSize τ c
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``Taint.RHint.toExprNS) tT instT hint)
  if h.isMVar then h.mvarId!.assign hv
  evalTactic (← `(tactic| lit_decide))

open Lean Elab Tactic in
/-- Proves `(Taint.checkR A S τ c ?hint).isSome = true` (or any decidable
equation about `Taint.checkR A S τ c ?hint`) as `taint_decide`, with the
relational summaries `S` in place of the analysis of each call that one of
them applies to (the first summary of a call of the same name that applies
from what is public there). `fillR S c hint = c`, which the hint then also
needs, is `rfl`. -/
elab "taint_decide_rel" : tactic => do
  let saved ← saveState
  try
    taintDecideRelAt (mkNatLit 1024)
  catch _ =>
    saved.restore
    taintDecideRelAt (mkConst ``Taint.chunk)

end VG
