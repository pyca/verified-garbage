module

public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Code as literals with shared blocks, for the kernel

The kernel evaluates the analysis of every block of a literal in full, even
of blocks equal to others it has analysed from the same taint: it does not
recognize two copies of a long list of instructions written out as the same
term. Code whose copies of a block are equal (e.g. field arithmetic with its
displacements erased, `Proof/Framework/X86_64/TaintErase.lean`) is analysed
much faster when every block is a constant: each distinct block is one
constant, whose analysis from the same taint the kernel evaluates once (as
for the templates of `Proof/Weierstrass/X86_64/FieldErase.lean`).

`materialize_shared N := t` defines `N.lit`, the value of the closed code
`t` as a literal whose distinct blocks are the constants `N.block<k>`, and
`N.lit_eq : t = N.lit`, which the kernel checks by evaluation (reading the
literals `t` reaches, as `materialize_code`). `lit_decide` and `taint_decide`
then rewrite `t` to `N.lit`, and compute their hints from `t`, in compiled
code. Unlike `materialize_code`, calls are written out in full, not as the
literals of their callees.
-/

public meta section

namespace VG

open Lean Meta Elab Command

namespace LitShare

/-- `e` (a code literal) with the list of each block replaced by a constant
`N.block<k>`, one for each distinct list. The state is the constants, and
what each subterm visited became. -/
meta partial def shareBlocks (N : Name) (e : Expr) :
    StateT (Std.HashMap Expr Name × Std.HashMap Expr Expr) MetaM Expr := do
  if e.isAppOfArity ``Code.block 3 then
    let l := e.appArg!
    let names := (← get).1
    if let some n := names[l]? then return mkApp e.appFn! (mkConst n)
    let n := N ++ Name.mkSimple s!"block{names.size}"
    addDecl (forceExpose := true) <| .defnDecl {
      name := n, levelParams := [], type := ← inferType l, value := l
      hints := .abbrev, safety := .safe }
    modify fun (names, m) => (names.insert l n, m)
    return mkApp e.appFn! (mkConst n)
  match e with
  | .app f a =>
    if let some e' := (← get).2[e]? then return e'
    let f' ← shareBlocks N f
    let a' ← shareBlocks N a
    let e' := .app f' a'
    modify fun (names, m) => (names, m.insert e e')
    return e'
  | .mdata _ b => shareBlocks N b
  | _ => return e

/-- Defines the blocks `N.block<k>`, `N.lit` and `N.lit_eq : code = N.lit`. -/
meta def materializeShared (N : Name) (code : Expr) : MetaM Unit := do
  let ty ← inferType code
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do
    throwError "materialize_shared: {code} is not code: {ty}"
  let codeTy := mkApp2 (mkConst ``Code) (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!)
  let v ← Lit.evalCode codeTy.appFn!.appArg! codeTy.appArg! code
  let (litV, _) ← (shareBlocks N (ShareCommon.shareCommon' v)).run ({}, {})
  addDecl (forceExpose := true) <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := litV
    hints := .abbrev, safety := .safe }
  -- `code = N.lit` by evaluation, of `code` with the literals it reaches if any.
  let prf ← match ← Lit.unfoldToLits N code with
    | some (_, prf) => pure prf
    | none => pure (mkApp2 (mkConst ``Eq.refl [1]) ty code)
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) ty code (mkConst (N ++ `lit))
    value := ShareCommon.shareCommon' prf }

end LitShare

/-- `materialize_shared N := t`: `N.lit`, the closed code `t` as a literal
whose distinct blocks are constants (`N.block<k>`), and `N.lit_eq : t = N.lit`,
which `lit_decide` and `taint_decide` read as they read `materialize_code`'s;
`materialize_shared c` does the same for the constant `c`, as `c.lit` and
`c.lit_eq`. A term `t` that contains code with a literal of its own is
rewritten to that literal first, so give such code a definition and
materialize the constant. -/
syntax "materialize_shared " ident (" := " term)? : command

elab_rules : command
  | `(materialize_shared $id:ident) => liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    unless (← getConstInfo c).levelParams.isEmpty do
      throwError "materialize_shared: {c} is universe polymorphic"
    LitShare.materializeShared c (mkConst c)
  | `(materialize_shared $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_shared: {e} is not closed"
    LitShare.materializeShared ((← getCurrNamespace) ++ id.getId) e

end VG
