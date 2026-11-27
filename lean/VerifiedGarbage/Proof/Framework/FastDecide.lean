module

public meta import Lean.Elab.Tactic.Basic

/-!
# `by decide` of facts about literals

Untrusted: this only changes how proofs are found.

Most proofs `by decide` are of facts about a few literals: a register is in a
list of registers or not, a list is contained in another, one number is below
another. `decide` searches for the instance of `Decidable`, evaluates it in the
elaborator and has the kernel evaluate it again: one to five milliseconds each,
a twentieth of the elaboration of the build. And before a tactic block inside a
term runs, the elaborator instantiates and shares every hypothesis' type
(`Term.runTactic`), as much again in a context of a hundred.

Here such a fact is evaluated directly (`holds?`), the instance is written down
(`inst?`), and the proof of a fact about the elements of an enumeration
compares their numbers (`Reg.ctorIdx`), which the kernel does natively
(`byNumbers?`). In a term of a module of `VerifiedGarbage.Proof`, `by decide` is
decided where it stands, with no tactic block (`elabByDecide`), once its
proposition has no metavariable. Any other fact, `decide` with an option, and
whatever `decide` fails on, is left to Lean's own `decide`
(`throwUnsupportedSyntax`).
-/

@[expose] public section

namespace VG.FastDecide

/-! ### Facts about lists of an enumeration's elements, by their numbers

`f` numbers the elements (`Reg.ctorIdx`); the kernel compares numbers natively. -/

/-- Whether no element of `l` has the number `n`. -/
noncomputable def allNe {α : Type} (f : α → Nat) (n : Nat) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => Bool.rec (motive := fun _ => Bool) ih false (Nat.beq (f b) n)) l

/-- The numbers of the elements of `l`, as a set of bits. -/
noncomputable def mask {α : Type} (f : α → Nat) (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (f b)) ih) l

theorem not_mem {α : Type} (f : α → Nat) {a : α} {l : List α} (h : allNe f (f a) l = true) : ¬ a ∈ l := by
  induction l with
  | nil => exact List.not_mem_nil
  | cons b l ih =>
    intro hm
    replace h : Bool.rec (motive := fun _ => Bool) (allNe f (f a) l) false (Nat.beq (f b) (f a)) = true := h
    cases hb : Nat.beq (f b) (f a) with
    | true => rw [hb] at h; cases h
    | false =>
      rw [hb] at h
      cases hm with
      | head => rw [Nat.beq_refl] at hb; cases hb
      | tail _ hm => exact ih h hm

theorem testBit_mask {α : Type} (f : α → Nat) (n : Nat) :
    ∀ l : List α, (mask f l).testBit n = true → ∃ b ∈ l, f b = n
  | [], h => by rw [show mask f [] = 0 from rfl, Nat.zero_testBit] at h; cases h
  | b :: l, h => by
    rw [show mask f (b :: l) = 1 <<< f b ||| mask f l from rfl, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨b, .head _, ?_⟩
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
        Nat.testBit_one_eq_true_iff_self_eq_zero] at h
      omega
    · obtain ⟨c, hc, e⟩ := testBit_mask f n l h
      exact ⟨c, .tail _ hc, e⟩

theorem mask_testBit {α : Type} (f : α → Nat) {a : α} {l : List α} (h : a ∈ l) : (mask f l).testBit (f a) = true := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [show mask f (b :: l) = 1 <<< f b ||| mask f l from rfl, Nat.testBit_or, Bool.or_eq_true]
    cases h with
    | head => left; rw [Nat.testBit_shiftLeft]; simp
    | tail _ h => exact .inr (ih h)

theorem mem {α : Type} (f : α → Nat) (g : Nat → α) (hg : ∀ x, g (f x) = x) {a : α} {l : List α}
    (h : Nat.testBit (mask f l) (f a) = true) : a ∈ l := by
  obtain ⟨b, hb, e⟩ := testBit_mask f _ l h
  rw [← hg a, ← e, hg]; exact hb

theorem subset {α : Type} (f : α → Nat) (g : Nat → α) (hg : ∀ x, g (f x) = x) {l m : List α}
    (h : Nat.beq (Nat.land (mask f l) (mask f m)) (mask f l) = true) : ∀ r, r ∈ l → r ∈ m := by
  intro r hr
  refine mem f g hg ?_
  have e : mask f l &&& mask f m = mask f l := Nat.eq_of_beq_eq_true h
  have := mask_testBit f hr
  rw [← e, Nat.testBit_and, Bool.and_eq_true] at this
  exact this.2

theorem ne {α : Type} (f : α → Nat) {a b : α} (h : Nat.beq (f a) (f b) = false) : ¬ a = b := by
  rintro rfl
  rw [Nat.beq_refl] at h; cases h

end VG.FastDecide

end

public meta section

namespace VG.FastDecide

open Lean Elab Term Meta

/-! ### Evaluation -/

/-- The value of a literal: a constructor of literals, or a number. -/
inductive Val where
  | ctor (c : Name) (args : List Val)
  | nat (n : Nat)
  deriving BEq

/-- The value of the term `e` (bound variables by `env`, the innermost first). -/
partial def val? (env : List Val) (e : Expr) : MetaM (Option Val) := do
  match e with
  | .bvar i => return env[i]?
  | .const c [] =>
    if let some (.ctorInfo i) := (← getEnv).find? c then
      if i.numParams == 0 && i.numFields == 0 then return some (.ctor c [])
    return none
  | .app (.app (.app (.app (.const ``Prod.mk _) _) _) a) b =>
    let some v ← val? env a | return none
    let some w ← val? env b | return none
    return some (.ctor ``Prod.mk [v, w])
  | .lit (.natVal n) => return some (.nat n)
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``Nat [])) (.lit (.natVal n))) _ => return some (.nat n)
  | .app (.app (.app (.app (.app (.app (.const c _) (.const ``Nat [])) (.const ``Nat [])) (.const ``Nat [])) _) a) b =>
    let op? : Option (Nat → Nat → Nat) := match c with
      | ``HAdd.hAdd => some (· + ·)
      | ``HMul.hMul => some (· * ·)
      | ``HSub.hSub => some (· - ·)
      | ``HDiv.hDiv => some (· / ·)
      | ``HMod.hMod => some (· % ·)
      | ``HPow.hPow => some (· ^ ·)
      | _ => none
    let some op := op? | return none
    let some (.nat m) ← val? env a | return none
    let some (.nat n) ← val? env b | return none
    if c == ``HPow.hPow && n > 4096 then return none
    return some (.nat (op m n))
  | _ => return none

/-- The values of the elements of the list `e`. -/
partial def vals? (env : List Val) (e : Expr) : MetaM (Option (List Val)) := do
  match e with
  | .app (.const ``List.nil _) _ => return some []
  | .app (.app (.app (.const ``List.cons _) _) a) l =>
    let some v ← val? env a | return none
    let some vs ← vals? env l | return none
    return some (v :: vs)
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _) _) _) _) _) a) b =>
    let some v ← vals? env a | return none
    let some w ← vals? env b | return none
    return some (v ++ w)
  | .app (.app (.app (.app (.const ``List.map _) _) _) f) l =>
    let i ← match f with
      | .app (.app (.const ``Prod.fst _) _) _ | .lam _ _ (.app (.app (.app (.const ``Prod.fst _) _) _) (.bvar 0)) _
      | .lam _ _ (.proj ``Prod 0 (.bvar 0)) _ => pure 0
      | .app (.app (.const ``Prod.snd _) _) _ | .lam _ _ (.app (.app (.app (.const ``Prod.snd _) _) _) (.bvar 0)) _
      | .lam _ _ (.proj ``Prod 1 (.bvar 0)) _ => pure 1
      | _ => return none
    let some vs ← vals? env l | return none
    return vs.mapM fun v => match v with
      | .ctor ``Prod.mk [a, b] => some (if i == 0 then a else b)
      | _ => none
  | .const c us =>
    let some (.defnInfo d) := (← getEnv).find? c | return none
    unless d.type.isAppOf ``List do return none
    vals? [] (d.value.instantiateLevelParams d.levelParams us)
  | _ => return none

/-- Whether the proposition `p` about literals holds. -/
partial def holds? (env : List Val) (p : Expr) : MetaM (Option Bool) := do
  match p with
  | .app (.const ``Not _) p => return (← holds? env p).map (!·)
  | .app (.app (.const ``And _) p) q =>
    match ← holds? env p with
    | some true => holds? env q
    | r => return r
  | .app (.app (.const ``Or _) p) q =>
    match ← holds? env p with
    | some false => holds? env q
    | r => return r
  | .app (.app (.app (.const ``Eq _) _) a) b =>
    let some v ← val? env a | return none
    let some w ← val? env b | return none
    return some (v == w)
  | .app (.app (.app (.const ``Ne _) _) a) b =>
    let some v ← val? env a | return none
    let some w ← val? env b | return none
    return some (v != w)
  | .app (.app (.app (.app (.app (.const ``Membership.mem _) _) (.app (.const ``List _) _)) _) l) a =>
    let some v ← val? env a | return none
    let some vs ← vals? env l | return none
    return some (vs.contains v)
  | .app (.app (.app (.app (.const c _) (.const ``Nat [])) _) a) b =>
    let some (.nat m) ← val? env a | return none
    let some (.nat n) ← val? env b | return none
    match c with
    | ``LT.lt => return some (m < n)
    | ``LE.le => return some (m ≤ n)
    | _ => return none
  | .forallE _ α (.forallE _ (.app (.app (.app (.app (.app (.const ``Membership.mem _) _)
      (.app (.const ``List _) _)) _) l) (.bvar 0)) q _) _ =>
    if α.isSort || l.hasLooseBVar 0 then return none
    let some vs ← vals? env (l.lowerLooseBVars 1 1) | return none
    for v in vs do
      -- The hypothesis is bound too, and not used.
      if q.hasLooseBVar 0 then return none
      match ← holds? (v :: env) (q.lowerLooseBVars 1 1) with
      | some true => pure ()
      | r => return r
    return some true
  | .forallE _ p q _ =>
    if q.hasLooseBVar 0 then return none
    match ← holds? env p with
    | some true => holds? env (q.lowerLooseBVars 1 1)
    | some false => return some true
    | none => return none
  | _ => return none

/-! ### Instances -/

/-- The instance of `DecidableEq α`. -/
def decEq? (α : Expr) : MetaM (Option Expr) := do
  if α.hasLooseBVars then return none
  synthInstance? (mkApp (mkConst ``DecidableEq [1]) α)

/-- An instance of `Decidable p`, for a `p` of those that `holds?` evaluates. -/
partial def inst? (p : Expr) : MetaM (Option Expr) := do
  match p with
  | .app (.const ``Not _) p =>
    return (← inst? p).map fun i => mkApp2 (mkConst ``instDecidableNot) p i
  | .app (.app (.const ``And _) p) q =>
    let some i ← inst? p | return none
    let some j ← inst? q | return none
    return some (mkApp4 (mkConst ``instDecidableAnd) p q i j)
  | .app (.app (.const ``Or _) p) q =>
    let some i ← inst? p | return none
    let some j ← inst? q | return none
    return some (mkApp4 (mkConst ``instDecidableOr) p q i j)
  | .app (.app (.app (.const ``Eq _) α) a) b => eqInst? α a b
  | .app (.app (.app (.const ``Ne us) α) a) b =>
    let some i ← eqInst? α a b | return none
    return some (mkApp2 (mkConst ``instDecidableNot) (mkApp3 (mkConst ``Eq us) α a b) i)
  | .app (.app (.app (.app (.app (.const ``Membership.mem _) α) (.app (.const ``List _) _)) _) l) a =>
    unless (← isType0 α) do return none
    let some d ← decEq? α | return none
    return some (mkAppN (mkConst ``List.instDecidableMemOfLawfulBEq [0]) #[α,
      mkApp2 (mkConst ``instBEqOfDecidableEq [0]) α d, mkApp2 (mkConst ``instLawfulBEq [0]) α d, a, l])
  | .app (.app (.app (.app (.const c _) (.const ``Nat [])) _) a) b =>
    match c with
    | ``LT.lt => return some (mkApp2 (mkConst ``Nat.decLt) a b)
    | ``LE.le => return some (mkApp2 (mkConst ``Nat.decLe) a b)
    | _ => return none
  | .forallE x α (.forallE _ (.app (.app (.app (.app (.app (.const ``Membership.mem _) _)
      (.app (.const ``List _) _)) _) l) (.bvar 0)) q _) _ =>
    if q.hasLooseBVar 0 || l.hasLooseBVar 0 then return none
    unless (← isType0 α) do return none
    let q := q.lowerLooseBVars 1 1
    let some i ← inst? q | return none
    return some (mkApp4 (mkConst ``List.decidableBAll [0]) α (.lam x α q .default) (.lam x α i .default)
      (l.lowerLooseBVars 1 1))
  | .forallE _ p q _ =>
    if q.hasLooseBVar 0 then return none
    let q := q.lowerLooseBVars 1 1
    let some i ← inst? p | return none
    let some j ← inst? q | return none
    return some (mkApp4 (mkConst ``instDecidableForall) p q i j)
  | _ => return none
where
  isType0 (α : Expr) : MetaM Bool := do
    return !α.hasLooseBVars && (← inferType α) == .sort 1
  eqInst? (α a b : Expr) : MetaM (Option Expr) := do
    if α.isConstOf ``Nat then return some (mkApp2 (mkConst ``instDecidableEqNat) a b)
    unless (← isType0 α) do return none
    let some d ← decEq? α | return none
    return some (mkApp2 d a b)

/-- The function that numbers the elements of the enumeration `α`, its inverse and the proof that it is. -/
def enum? (α : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let .const c [] := α | return none
  unless (← inferType α) == .sort 1 do return none
  let env ← getEnv
  let f := c.str "ctorIdx"
  let g := c.str "ofNat"
  let h := c.str "ofNat_ctorIdx"
  unless env.contains f && env.contains g && env.contains h do return none
  return some (mkConst f, mkConst g, mkConst h)

private def reflBool (b : Name) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst b)

/-- A proof of `p`, which holds, if it is of those the kernel checks by the elements' numbers. -/
def byNumbers? (p : Expr) : MetaM (Option Expr) := do
  match p with
  | .app (.const ``Not _) (.app (.app (.app (.app (.app (.const ``Membership.mem _) α)
      (.app (.const ``List _) _)) _) l) a) =>
    let some (f, _, _) ← enum? α | return none
    return some (mkAppN (mkConst ``not_mem) #[α, f, a, l, reflBool ``true])
  | .app (.app (.app (.app (.app (.const ``Membership.mem _) α) (.app (.const ``List _) _)) _) l) a =>
    let some (f, g, h) ← enum? α | return none
    return some (mkAppN (mkConst ``mem) #[α, f, g, h, a, l, reflBool ``true])
  | .forallE _ α (.forallE _ (.app (.app (.app (.app (.app (.const ``Membership.mem _) _)
      (.app (.const ``List _) _)) _) l) (.bvar 0))
      (.app (.app (.app (.app (.app (.const ``Membership.mem _) _) (.app (.const ``List _) _)) _) m) (.bvar 1)) _) _ =>
    if l.hasLooseBVars || m.hasLooseBVars then return none
    let some (f, g, h) ← enum? α | return none
    return some (mkAppN (mkConst ``subset) #[α, f, g, h, l, m, reflBool ``true])
  | .app (.app (.app (.const ``Ne _) α) a) b | .app (.const ``Not _) (.app (.app (.app (.const ``Eq _) α) a) b) =>
    let some (f, _, _) ← enum? α | return none
    return some (mkAppN (mkConst ``ne) #[α, f, a, b, reflBool ``false])
  | _ => return none

/-- The proof by `decide` of `p`, if it is of the propositions evaluated here and true. -/
partial def prove? (p : Expr) : MetaM (Option Expr) := do
  match p with
  | .app (.app (.const ``And _) p) q =>
    let some h ← prove? p | return none
    let some k ← prove? q | return none
    return some (mkApp4 (mkConst ``And.intro) p q h k)
  | .forallE x p q bi =>
    if !q.hasLooseBVar 0 then
      let q := q.lowerLooseBVars 1 1
      if (← holds? [] q) == some true then
        if let some h ← prove? q then return some (.lam x p h bi)
  | _ => pure ()
  let some true ← holds? [] p | return none
  if let some e ← byNumbers? p then return some e
  let some i ← inst? p | return none
  let eq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp2 (mkConst ``Decidable.decide) p i) (mkConst ``true)
  return some (mkApp3 (mkConst ``of_decide_eq_true) p i (mkExpectedPropHint reflBoolTrue eq))

/-! ### The tactic and the term -/

@[tactic Lean.Parser.Tactic.decide]
def evalDecideFast : Tactic.Tactic := fun stx => do
  unless stx[1][0].getNumArgs == 0 do throwUnsupportedSyntax
  let g ← Tactic.getMainGoal
  let p ← instantiateMVars (← g.getType)
  if p.hasFVar || p.hasMVar then throwUnsupportedSyntax
  let some e ← prove? p | throwUnsupportedSyntax
  g.assign e
  Tactic.replaceMainGoal []

/-- Whether `stx` is `by decide`. -/
def isByDecide (stx : Syntax) : Bool :=
  let seq := stx[1][0]
  seq.isOfKind ``Lean.Parser.Tactic.tacticSeq1Indented && seq[0].getNumArgs == 1 &&
    seq[0][0].isOfKind ``Lean.Parser.Tactic.decide && seq[0][0][1][0].getNumArgs == 0

/-- The proof by `decide` of `p`, if it holds and `decide` finds it. -/
def decide? (p : Expr) : MetaM (Option Expr) := do
  if let some e ← prove? p then return some e
  if (← holds? [] p) == some false then return none
  -- The evaluation `decide` does. Where it fails, so does `decide`.
  let some inst ← synthInstance? (mkApp (mkConst ``Decidable) p) | return none
  let dec := mkApp2 (mkConst ``Decidable.decide) p inst
  unless (← withAtLeastTransparency .default <| whnf dec).isConstOf ``true do return none
  let eq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) dec (mkConst ``true)
  return some (mkApp3 (mkConst ``of_decide_eq_true) p inst (mkExpectedPropHint reflBoolTrue eq))

@[term_elab Lean.Parser.Term.byTactic]
def elabByDecide : TermElab := fun stx expectedType? => do
  unless isByDecide stx do throwUnsupportedSyntax
  let some p := expectedType? | throwUnsupportedSyntax
  if (← getEnv).isExporting || (← read).tacSnap?.isSome then throwUnsupportedSyntax
  unless (`VerifiedGarbage.Proof).isPrefixOf (← getEnv).mainModule do throwUnsupportedSyntax
  let p ← instantiateMVars p
  if p.hasExprMVar then
    tryPostpone
    throwUnsupportedSyntax
  if p.hasFVar || p.hasMVar then throwUnsupportedSyntax
  let some e ← decide? p | throwUnsupportedSyntax
  -- What the tactic block would leave: the linters take the variables its metavariables are assigned
  -- for used.
  let mctx ← getMCtx
  pushInfoLeaf <| .ofTacticInfo
    { elaborator := `VG.FastDecide.elabByDecide, stx
      mctxBefore := mctx, goalsBefore := [], mctxAfter := mctx, goalsAfter := [] }
  return e

end VG.FastDecide
