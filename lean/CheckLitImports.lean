import Lean

/-!
# Kernel checks that evaluate code without its literal

`lit_decide`, `taint_decide` and the registrations' default proofs
(`Code.all_of_allInstrs (by lit_decide)`) have the kernel evaluate code, with
each code that has a literal (`materialize_code` and the other commands of
`Proof/Framework/Lit.lean`) rewritten to it: but only the literals the module
sees, those of its imports and of what they `public import`. Code whose
literal the module does not see is built again by the kernel, from the
functions that build it (a register allocator, unrolled rounds, tables), in
every check: seconds where reading the literal takes milliseconds.

`lake env lean --run CheckLitImports.lean FILE` imports the modules listed
in FILE (one per line, as the registration files, which reach every proof
of an artifact) and prints, for each proposition the kernel decides
(`of_decide_eq_true p _ _` at the head of a declaration, as `decide +kernel`
leaves it) that mentions code leading to a constant with a literal, a line

  `<module> TAB <declaration> TAB <code> TAB <literal> TAB <literal's module> TAB <seen>`

where `<seen>` is `seen` when the module sees the literal (so the check did
not rewrite it: `decide +kernel` where `lit_decide` belongs, or code `rw_lit`
does not find), and `unseen` otherwise (import the literal's module). Only
literals the module could import are reported: not those whose module
imports it. A file that is not a module imports the modules' private
imports too, so the environment has every literal they reach.
`ci/lit_imports.py` runs it and weighs each line by the kernel time
the build's profile records for the declaration.
-/

open Lean

/-- Modules of the code and proofs, whose definitions can lead to code with
a literal (as `VG.codeModule` in `Proof/Framework/Lit.lean`). -/
def codeModule (m : Name) : Bool :=
  match m.components with
  | `VerifiedGarbage :: `Proof :: `Framework :: _ => false
  | `VerifiedGarbage :: k :: _ => k ∈ [`Impl, `Proof, `Variants, `Generic, `Artifacts]
  | _ => false

/-- The constants with a literal (`c.lit_eq : c = c.lit`, or `c x₁ … = N.lit`
for a template) that the definition `c` leads to, memoized. -/
partial def reached (env : Environment) (mods : Array Name) (lits : NameMap (Array (Name × Name))) (c : Name) :
    StateM (NameMap NameSet) NameSet := do
  if let some r := (← get).find? c then return r
  modify (·.insert c {})
  let mut r : NameSet := if lits.contains c then NameSet.empty.insert c else {}
  if let some i := env.getModuleIdxFor? c then
    if codeModule mods[i.toNat]! then
      if let some (.defnInfo d) := env.find? c then
        for u in d.value.getUsedConstants do
          unless u matches .str _ "lit" do
            r := (← reached env mods lits u).foldl (·.insert ·) r
  modify (·.insert c r)
  return r

/-- The proposition the kernel decides at the head of `e`, under binders. -/
partial def decided? (e : Expr) : Option Expr :=
  match e with
  | .lam _ _ b _ | .mdata _ b => decided? b
  | _ => if e.isAppOfArity ``of_decide_eq_true 3 then some (e.getArg! 0) else none

/-- Whether module `a` imports `b`, transitively. -/
partial def importsMod (env : Environment) (idx : NameMap Nat) (a b : Name) :
    StateM NameSet Bool := do
  if a == b then return true
  if (← get).contains a then return false
  modify (·.insert a)
  let some i := idx.find? a | return false
  for imp in env.header.moduleData[i]!.imports do
    if ← importsMod env idx imp.module b then return true
  return false

/-- The modules `m` sees: its imports and, transitively, what they `public import`. -/
partial def sees (env : Environment) (idx : NameMap Nat) (m : Name) : NameSet := Id.run do
  let imps (n : Name) := match idx.find? n with
    | some i => env.header.moduleData[i]!.imports
    | none => #[]
  let mut seen : NameSet := {}
  let mut todo := (imps m).map (·.module)
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    for imp in imps n do
      if imp.isExported then todo := todo.push imp.module
  return seen

def main (args : List String) : IO UInt32 := do
  let [file] := args | IO.eprintln "usage: CheckLitImports.lean FILE"; return 2
  initSearchPath (← findSysroot)
  let roots := (← IO.FS.lines file).filter (!·.isEmpty)
  let env ← importModules (roots.map fun m => { module := m.toName }) {}
  let mods := env.header.moduleNames
  let idx : NameMap Nat := mods.size.fold (fun i _ acc => acc.insert mods[i] i) {}
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => mods[i.toNat]!
    | none => .anonymous
  -- Each constant with a literal, and the module of the literal.
  -- (Code as `.block [...]` is no constant: only code a constant of the
  -- project names, or a template's function, can be reached.)
  let mut lits : NameMap (Array (Name × Name)) := {}
  for (n, ci) in env.constants.map₁.toList do
    if let .str p "lit_eq" := n then
      if env.contains (.str p "lit") then
        if let some (_, lhs, _) := ci.type.eq? then
          -- A literal of an application (a template, `f x` for some `x`) is
          -- not one of every use of `f`: only literals of constants count.
          if let .const c _ := lhs then
            if codeModule (modOf c) then
              lits := lits.insert c ((lits.find? c |>.getD #[]).push (modOf n, p))
  let mut memo : NameMap NameSet := {}
  let mut seesMemo : NameMap NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    let m := modOf n
    unless codeModule m do continue
    if n matches .str _ "lit_eq" then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let some p := decided? v | continue
    for u in p.getUsedConstants do
      if u matches .str _ "lit" then continue
      let (r, memo') := (reached env mods lits u).run memo
      memo := memo'
      for t in r do
        let s ← match seesMemo.find? m with
          | some s => pure s
          | none => do
            let s := sees env idx m
            seesMemo := seesMemo.insert m s
            pure s
        for (l, lit) in (lits.find? t).getD #[] do
          if l == m then continue
          -- A literal whose module imports `m` cannot be imported by it.
          if ((importsMod env idx l m).run' {} : Id Bool).run then continue
          IO.println s!"{m}\t{n}\t{u}\t{t}\t{l}\t{if s.contains l then "seen" else "unseen"}\t{lit}"
  return 0
