module

public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Literals of code reached by other arguments

`unfoldToLits` rewrites an application `f x₁ … xₖ` to the literal `M.lit` of
`materialize_code M := f x₁ … xₖ` only where the code writes it with the same
arguments: code built from a configuration reaches the field arithmetic as
`mulFn p521.SP.k p521.SP.m` (or its configuration unfolded), not as the
literal's `mulFn p521p.k p521p.m`. The kernel then evaluates the function
again in the literal of every such caller (P-521's x86 product: seconds).

`materialize_aliases t` finds, in the closed code `t` as `unfoldToLits`
leaves it, each application of the function of such a literal `M` to other
arguments that the kernel finds equal to `M`'s, and defines `N.lit := M.lit`
and `N.lit_eq : (that application) = N.lit`, proven by `M.lit_eq`, for a new
`N`. A later `materialize_shared` or `materialize_code` of `t` then reads
`M`'s literal there.
-/

public meta section

namespace VG

open Lean Meta Elab Command

namespace LitAlias

/-- The code of each literal `M`: the application `M.lit_eq` states, or the
value of the constant it states, if an application of a function to closed
arguments (not a template's function). -/
meta def patterns : MetaM (Array (Name × Expr)) := do
  let env ← getEnv
  let mut out := #[]
  for M in Lit.litNames env do
    let lhs ← Lit.lhsOf M
    let pat := match lhs with
      | .const c _ => match env.find? c with
        | some (.defnInfo d) => if d.levelParams.isEmpty then some d.value else none
        | _ => none
      | _ => some lhs
    let some pat := pat | continue
    if pat.getAppFn.isConst && pat.getAppNumArgs > 0 && !pat.hasLooseBVars && !pat.hasFVar &&
        !pat.hasMVar && !(← whnfD (← inferType pat)).isForall then
      out := out.push (M, pat)
  return out

/-- The aliases of the literals that `x` reaches by other arguments, named
`N.alias<k>`, from `k₀`; the next `k`. -/
meta def aliasRound (N : Name) (x : Expr) (k₀ : Nat) : MetaM Nat := do
  let env ← getEnv
  let pats ← patterns
  if pats.isEmpty then return k₀
  let heads := pats.foldl (fun s (_, l) => s.insert l.getAppFn.constName!) ({} : NameSet)
  -- The code as `unfoldToLits` leaves it, or, where it reaches no literal yet,
  -- unfolded as it would be once these functions have literals.
  let e ← match ← Lit.unfoldToLits .anonymous x with
    | some (e, _) => pure e
    | none =>
      let mods := env.header.moduleNames
      let mut memo : NameMap Bool := {}
      for u in x.getUsedConstants do
        if !heads.contains u then
          (_, memo) ← (Lit.reaches heads mods (Lit.firstModuleOf env heads) u).run memo
      let memo' := memo
      pure (Lit.unfoldWhere env (fun c => memo'.find? c == some true) x
        (fun t => t.getAppFn.isConst && heads.contains t.getAppFn.constName!))
  let found ← IO.mkRef (#[] : Array Expr)
  e.forEach fun t => do
    if t.getAppFn.isConst && heads.contains t.getAppFn.constName! && !t.hasLooseBVars &&
        !t.hasFVar && !t.hasMVar && !(← found.get).contains t then
      found.modify (·.push t)
  let mut k := k₀
  for t in ← found.get do
    if pats.any (·.2 == t) then continue
    let some (M, _) := pats.find? fun (_, l) =>
        l.getAppFn == t.getAppFn && l.getAppNumArgs == t.getAppNumArgs &&
          -- Argument by argument: the kernel would evaluate unequal applications.
          (t.getAppArgs.zip l.getAppArgs).all fun (a, b) => Kernel.isDefEqGuarded env {} a b
      | continue
    let A := N ++ Name.mkSimple s!"alias{k}"
    k := k + 1
    let ty ← inferType t
    let u ← getLevel ty
    addDecl (forceExpose := true) <| .defnDecl {
      name := A ++ `lit, levelParams := [], type := ty, value := mkConst (M ++ `lit)
      hints := .abbrev, safety := .safe }
    addDecl <| .thmDecl {
      name := A ++ `lit_eq, levelParams := [],
      type := mkApp3 (mkConst ``Eq [u]) ty t (mkConst (A ++ `lit))
      value := mkConst (M ++ `lit_eq) }
  return k

/-- The aliases, in rounds until `unfoldToLits` leaves no application to alias. -/
meta def materializeAliases (N : Name) (x : Expr) : MetaM Unit := do
  let mut k := 0
  for _ in [0:4] do
    let k' ← aliasRound N x k
    if k' == k then return
    k := k'

end LitAlias

/-- `materialize_aliases N := t`: for each application in the closed code `t`
of the function of a literal `M` (`materialize_code M := f x₁ … xₖ`) to
arguments the kernel finds equal to `M`'s but written otherwise,
`N.alias<k>.lit := M.lit` and `N.alias<k>.lit_eq`, so that a literal of `t`
reads `M.lit` there rather than evaluating `f` again. -/
syntax "materialize_aliases " ident " := " term : command

elab_rules : command
  | `(materialize_aliases $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_aliases: {e} is not closed"
    LitAlias.materializeAliases ((← getCurrNamespace) ++ id.getId) e

end VG
