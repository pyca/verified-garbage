module

public import Init.Data.Nat.Internal.Linear
public import Init.Omega
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Simp.Arith.Nat.Basic
public meta import Lean.Meta.Offset
public meta import Lean.Meta.AppBuilder

/-!
# Small linear goals over `Nat`, from at most two hypotheses

Untrusted: this only changes how proofs are found.

The proofs' arithmetic goals are small (`a + 8 * i + 8 ≤ n`), and most need
one hypothesis, or none (`Omega.lean`). `omega` takes about ten milliseconds
for such a goal however few facts it is given, more than half of it the
kernel's, which checks everything `omega` made of the problem.

`lin?` proves a goal `p ≤ q`, `p < q` or `p = q` between linear terms over
`Nat` from at most two facts of those forms, where a sum of the facts, each
taken some number of times, gives the goal: `p + k * b ≤ q + k * a` holds
whatever the atoms are, for a fact `a ≤ b` (`of₁`, and `of₂` for two). That
one inequality is all the kernel checks, by evaluating its normal form
(`Nat.Internal.Linear`, which `simp +arith` uses): the terms are read once,
into expressions over the same atoms, and their meaning there is the terms
themselves, by unfolding.

A term that is not a sum, a product by a numeral or a numeral (a
subtraction, a quotient, a length) is an atom; a closed term (`2 ^ 64`) is
its value. Anything else (another type, `∨`, `¬`, a goal that needs three
facts or a case split) is left to `omega`: `lin?` then returns `false`
without changing anything.
-/

@[expose] public section

namespace VG.Lin

open Nat.Internal.Linear

/-- A goal that holds whatever its atoms are. -/
theorem of₀ (ctx : Context) (p q : Expr)
    (v : ({ eq := false, lhs := p, rhs := q } : ExprCnstr).toNormPoly.isValid = true) :
    p.denote ctx ≤ q.denote ctx :=
  of_eq_true (ExprCnstr.eq_true_of_isValid ctx { eq := false, lhs := p, rhs := q } v)

/-- A goal from `k` times a fact `a ≤ b`. -/
theorem of₁ (ctx : Context) (p q a b : Expr) (k : Nat)
    (v : ({ eq := false, lhs := .add p (.mulL k b), rhs := .add q (.mulL k a) } : ExprCnstr).toNormPoly.isValid
      = true)
    (h : a.denote ctx ≤ b.denote ctx) : p.denote ctx ≤ q.denote ctx := by
  have hv : p.denote ctx + k * b.denote ctx ≤ q.denote ctx + k * a.denote ctx :=
    of_eq_true (ExprCnstr.eq_true_of_isValid ctx
      { eq := false, lhs := .add p (.mulL k b), rhs := .add q (.mulL k a) } v)
  have hk := Nat.mul_le_mul_left k h
  omega

/-- A goal from `k₁` times a fact `a₁ ≤ b₁` and `k₂` times a fact `a₂ ≤ b₂`. -/
theorem of₂ (ctx : Context) (p q a₁ b₁ a₂ b₂ : Expr) (k₁ k₂ : Nat)
    (v : ({ eq := false, lhs := .add (.add p (.mulL k₁ b₁)) (.mulL k₂ b₂),
            rhs := .add (.add q (.mulL k₁ a₁)) (.mulL k₂ a₂) } : ExprCnstr).toNormPoly.isValid = true)
    (h₁ : a₁.denote ctx ≤ b₁.denote ctx) (h₂ : a₂.denote ctx ≤ b₂.denote ctx) :
    p.denote ctx ≤ q.denote ctx := by
  have hv : p.denote ctx + k₁ * b₁.denote ctx + k₂ * b₂.denote ctx ≤
      q.denote ctx + k₁ * a₁.denote ctx + k₂ * a₂.denote ctx :=
    of_eq_true (ExprCnstr.eq_true_of_isValid ctx
      { eq := false, lhs := .add (.add p (.mulL k₁ b₁)) (.mulL k₂ b₂),
        rhs := .add (.add q (.mulL k₁ a₁)) (.mulL k₂ a₂) } v)
  have hk₁ := Nat.mul_le_mul_left k₁ h₁
  have hk₂ := Nat.mul_le_mul_left k₂ h₂
  omega

end VG.Lin

end

public meta section

namespace VG.Lin

open Lean Meta Elab Tactic
open Lean.Meta.Simp.Arith.Nat (LinearExpr toContextExpr)

/-- The atoms read so far. -/
abbrev M := StateRefT (Array Expr) MetaM

def atom (e : Expr) : M LinearExpr := do
  let atoms ← get
  match atoms.findIdx? (· == e) with
  | some i => return .var i
  | none =>
    set (atoms.push e)
    return .var atoms.size

/-- `e : Nat` as a linear expression over the atoms: a closed term is its
value, and a term that is neither a sum nor a product by a numeral is an atom. -/
partial def toLin (e : Expr) : M LinearExpr := do
  let e := e.consumeMData
  if !e.hasFVar && !e.hasMVar then
    if let some n ← (evalNat e).run then return .num n
  match_expr e with
  | HAdd.hAdd α _ _ _ a b =>
    if α.isConstOf ``Nat then return .add (← toLin a) (← toLin b) else atom e
  | Nat.succ a => return .add (← toLin a) (.num 1)
  | HMul.hMul α _ _ _ a b =>
    if α.isConstOf ``Nat then
      if let some k ← (evalNat a).run then return .mulL k (← toLin b)
      if let some k ← (evalNat b).run then return .mulL k (← toLin a)
    atom e
  | _ => atom e

/-- A fact `lhs ≤ rhs` between linear expressions, as a function that gives its
proof from a proof of the proposition it was read from. -/
structure Le where
  lhs : LinearExpr := .num 0
  rhs : LinearExpr := .num 0
  /-- The proof of `lhs ≤ rhs` (which the proposition is, by unfolding: `a < b`
  is `a + 1 ≤ b`), from the proposition's. -/
  proof : Expr → Expr := id
  deriving Inhabited

/-- The inequalities `ty`, a proposition over `Nat`, gives: one for `≤`, `<`,
`≥` and `>`, two for `=`; none for anything else. -/
def toLes (ty : Expr) : M (Array Le) := do
  let ty := ty.consumeMData
  let isNat (α : Expr) := α.isConstOf ``Nat
  match_expr ty with
  | LE.le α _ a b =>
    if isNat α then return #[⟨← toLin a, ← toLin b, id⟩] else return #[]
  | GE.ge α _ a b =>
    if isNat α then return #[⟨← toLin b, ← toLin a, id⟩] else return #[]
  | LT.lt α _ a b =>
    if isNat α then return #[⟨.add (← toLin a) (.num 1), ← toLin b, id⟩] else return #[]
  | GT.gt α _ a b =>
    if isNat α then return #[⟨.add (← toLin b) (.num 1), ← toLin a, id⟩] else return #[]
  | Eq α a b =>
    if isNat α then
      let la ← toLin a
      let lb ← toLin b
      return #[⟨la, lb, fun h => mkApp3 (mkConst ``Nat.le_of_eq) a b h⟩,
               ⟨lb, la, fun h => mkApp3 (mkConst ``Nat.le_of_eq) b a
                 (mkApp4 (mkConst ``Eq.symm [1]) (mkConst ``Nat) a b h)⟩]
    else return #[]
  | _ => return #[]

/-- A linear expression as its coefficients: of each atom, and the constant
(at the index of no atom). -/
def coeffs (n : Nat) (e : LinearExpr) : Array Int :=
  go 1 e (Array.replicate (n + 1) 0)
where
  go (c : Nat) : LinearExpr → Array Int → Array Int
    | .num k, acc => acc.modify n (· + (c * k : Nat))
    | .var i, acc => acc.modify i (· + (c : Nat))
    | .add a b, acc => go c b (go c a acc)
    | .mulL k a, acc => go (c * k) a acc
    | .mulR a k, acc => go (c * k) a acc

/-- The least `k` with `d - k * e ≥ 0` in every coefficient, if there is one:
how many times a fact with `rhs - lhs = e` gives a goal with `rhs - lhs = d`. -/
def times? (d e : Array Int) : Option Nat := Id.run do
  let mut lo : Int := 0
  let mut hi : Option Int := none
  for i in [0:d.size] do
    let di := d[i]!
    let ei := e[i]!
    if ei < 0 then
      -- `di - k * ei ≥ 0` from `k ≥ ⌈di / ei⌉` on (both negative when it matters)
      if di < 0 then lo := max lo ((-di + (-ei) - 1) / (-ei))
    else if ei == 0 then
      if di < 0 then return none
    else
      if di < 0 then return none
      let b := di / ei
      hi := some (match hi with | some h => min h b | none => b)
  match hi with
  | some h => if lo ≤ h then some lo.toNat else none
  | none => some lo.toNat

/-- A proof of the goal `g` from the facts `fs` (proofs of propositions over
`Nat`), if a sum of at most two of them, each taken some number of times,
gives it: see the module's docs. -/
def prove? (g : Expr) (fs : Array Expr) : MetaM (Option Expr) := do
  let read : M (Array Le × Array (Le × Expr)) := do
    let goals ← toLes g
    let mut facts : Array (Le × Expr) := #[]
    unless goals.isEmpty do
      for f in fs do
        for le in ← toLes (← instantiateMVars (← inferType f)) do
          facts := facts.push (le, le.proof f)
    return (goals, facts)
  let ((goals, facts), atoms) ← read.run #[]
  -- `p = q` is both inequalities, each proven on its own: only `≤`, `<`, `≥`, `>` here.
  let #[goal] := goals | return none
  let n := atoms.size
  let d := (coeffs n goal.rhs).zipWith (· - ·) (coeffs n goal.lhs)
  let es := facts.map fun (le, _) => (coeffs n le.rhs).zipWith (· - ·) (coeffs n le.lhs)
  let ctx ← toContextExpr atoms
  let finish (e : Expr) : MetaM (Option Expr) := return some (mkExpectedPropHint e g)
  let p := toExpr goal.lhs
  let q := toExpr goal.rhs
  if d.all (· ≥ 0) then
    return ← finish (mkApp4 (mkConst ``VG.Lin.of₀) ctx p q eagerReflBoolTrue)
  for i in [0:facts.size] do
    if let some k := times? d es[i]! then
      let (le, h) := facts[i]!
      return ← finish (mkApp8 (mkConst ``VG.Lin.of₁) ctx p q (toExpr le.lhs) (toExpr le.rhs) (mkNatLit k)
        eagerReflBoolTrue h)
  -- Two facts: the first as few times as leaves a goal the second gives.
  for i in [0:facts.size] do
    for j in [0:facts.size] do
      if i == j then continue
      for k₁ in [1:9] do
        let d' := d.zipWith (fun (x y : Int) => x - (k₁ : Int) * y) es[i]!
        if let some k₂ := times? d' es[j]! then
          let (le₁, h₁) := facts[i]!
          let (le₂, h₂) := facts[j]!
          return ← finish (mkAppN (mkConst ``VG.Lin.of₂)
            #[ctx, p, q, toExpr le₁.lhs, toExpr le₁.rhs, toExpr le₂.lhs, toExpr le₂.rhs, mkNatLit k₁, mkNatLit k₂,
              eagerReflBoolTrue, h₁, h₂])
  return none

/-- Closes the main goal with `prove?` from the facts `fs`, if it can: whether it did. -/
def lin? (fs : Array Expr) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some proof ← prove? ty fs | return false
    g.assign proof
    replaceMainGoal []
    return true

/-- `vg_lin`: a linear goal over `Nat` from at most two of the hypotheses
(`lin?`), or an error. -/
elab "vg_lin" : tactic => do
  let fs ← withMainContext getLocalHyps
  unless ← lin? fs do throwError "vg_lin: not a sum of at most two hypotheses"

end VG.Lin
