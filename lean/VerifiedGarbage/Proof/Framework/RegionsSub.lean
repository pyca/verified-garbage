module

public import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Simp

/-!
# `regions_sub`: one list literal's elements among another's

`regions_sub` proves `∀ r ∈ l₁, r ∈ l₂` for list literals `l₁` and `l₂` whose
elements are in `l₂` as they are written (as `Frame.mono` and the like need):
it finds each element of `l₁` in `l₂` and builds the membership proof
directly, without `simp`. Any other goal it leaves to `simp`.
-/

public meta section

namespace VG.RegionsSub

open Lean Elab Tactic Meta
open Lean Elab Tactic Meta

/-- The elements of a list literal. -/
partial def rsElems (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.cons 3 then (e.getArg! 1 :: ·) <$> rsElems (e.getArg! 2)
  else if e.isAppOfArity ``List.nil 1 then some [] else none

/-- A proof of `a ∈ l`, `a` the `j`-th element of the literal `l`. -/
def rsMem (u : Level) (α a l : Expr) : Nat → Expr
  | 0 => mkApp3 (mkConst ``List.mem_cons_self [u]) α a (l.getArg! 2)
  | j + 1 => mkApp5 (mkConst ``List.mem_cons_of_mem [u]) α (l.getArg! 1) a (l.getArg! 2)
      (rsMem u α a (l.getArg! 2) j)

/-- `∀ x ∈ l, p x`, from a proof of `p` for each element of the literal `l`. -/
def rsAll (u : Level) (α p : Expr) : Expr → List Expr → Expr
  | l, h :: hs =>
    let a := l.getArg! 1; let t := l.getArg! 2
    let iff := mkApp4 (mkConst ``List.forall_mem_cons [u]) α p a t
    let lhs := mkForall `x .default α (mkForall `h .default (mkApp5 (mkConst ``Membership.mem [u, u]) α
      (mkApp (mkConst ``List [u]) α) (mkApp (mkConst ``List.instMembership [u]) α) l (.bvar 0)) (mkApp p (.bvar 1)))
    let rhs := mkAnd (mkApp p a) (mkForall `x .default α (mkForall `h .default (mkApp5 (mkConst ``Membership.mem [u, u]) α
      (mkApp (mkConst ``List [u]) α) (mkApp (mkConst ``List.instMembership [u]) α) t (.bvar 0)) (mkApp p (.bvar 1))))
    mkApp4 (mkConst ``Iff.mpr) lhs rhs iff
      (mkApp4 (mkConst ``And.intro) (mkApp p a) (mkForall `x .default α (mkForall `h .default (mkApp5 (mkConst ``Membership.mem [u, u]) α
      (mkApp (mkConst ``List [u]) α) (mkApp (mkConst ``List.instMembership [u]) α) t (.bvar 0)) (mkApp p (.bvar 1)))) h (rsAll u α p t hs))
  | _, [] => mkApp2 (mkConst ``List.forall_mem_nil [u]) α p

elab "regions_sub" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let r ← (do
    let .forallE _ α (.forallE _ h1 h2 _) _ := t | return none
    let_expr Membership.mem _ _ _ l₁ x₁ := h1 | return none
    let_expr Membership.mem _ _ _ l₂ x₂ := h2 | return none
    unless x₁ == .bvar 0 && x₂ == .bvar 1 && !l₁.hasLooseBVars && !l₂.hasLooseBVars do return none
    let some xs := rsElems l₁ | return none
    let some ys := rsElems l₂ | return none
    let some js := xs.mapM (fun x => ys.findIdx? (· == x)) | return none
    let .succ u ← getLevel α | return none
    let p := mkLambda `x .default α (mkApp5 (mkConst ``Membership.mem [u, u]) α
      (mkApp (mkConst ``List [u]) α) (mkApp (mkConst ``List.instMembership [u]) α) l₂ (.bvar 0))
    return some (rsAll u α p l₁ ((xs.zip js).map fun (x, j) => rsMem u α x l₂ j)) : TacticM (Option Expr))
  match r with
  | some pf =>
    if ← withReducible (isDefEq (← inferType pf) t) then g.assign pf; replaceMainGoal []
    else evalTactic (← `(tactic| simp))
  | none => evalTactic (← `(tactic| simp))

end VG.RegionsSub
