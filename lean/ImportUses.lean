import Lean

/-!
# What each module's imports are used for

For `ci/modularize.py visibility`: imports the modules named on the command
line (every module of the library, after `lake build`) and writes, for each
module of the imported closure, one line of tab-separated fields:

* its name;
* its imports, as `name` followed by flags, `+p` for `public` and `+m` for
  `meta`, comma-separated;
* for a module of this project (`VerifiedGarbage.…`), the other modules whose
  constants occur in its public surface: the types of its declarations, the
  values of its definitions, and the values of the auxiliary theorems those
  refer to (`_proof_…`), closed over the declarations of the module they
  refer to;
* the other modules whose constants occur anywhere in it, proofs included;
* `meta` if it declares syntax, macros, elaborators or simprocs (by the types
  of its constants), else `-`.

Run it from `lean/`: `lake env lean --run ImportUses.lean OUT MODULE…`.
-/

open Lean

/-- Types whose constants make a module one that changes how others parse
or elaborate, rather than only what they can refer to. -/
def metaTypes : List Name :=
  [``ParserDescr, ``TrailingParserDescr, ``Lean.Parser.Parser, ``Lean.Parser.TrailingParser,
   ``Macro, ``Lean.Elab.Term.TermElab, ``Lean.Elab.Tactic.Tactic, ``Lean.Elab.Command.CommandElab,
   ``Lean.Meta.Simp.Simproc, ``Lean.Meta.Simp.DSimproc, ``Lean.PrettyPrinter.Unexpander,
   ``Lean.PrettyPrinter.Delaborator.Delab]

/-- Whether `n` is an auxiliary declaration a definition's value may refer to,
whose value belongs to that definition's surface. -/
def isAux (n : Name) : Bool :=
  n.isInternal || match n with
    | .str _ s => s.startsWith "proof_" || s.startsWith "_proof" || s.startsWith "_auxLemma"
    | _ => false

def main (args : List String) : IO Unit := do
  let out :: roots := args | throw <| IO.userError "usage: ImportUses.lean OUT MODULE…"
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map ({ module := ·.toName })) {} (trustLevel := 1024)
    (loadExts := false)
  let mods := env.header.moduleNames
  -- A constant that several modules realize independently (an equation lemma,
  -- `congr_simp`) is recorded once, at one of them: attribute it to one the
  -- module imports (its closure, a bit set over module indices, in which a
  -- module's imports come before it).
  let mut clo : Array Nat := #[]
  for i in [0:mods.size] do
    let mut c := 1 <<< i
    for im in env.header.moduleData[i]!.imports do
      if let some j := env.getModuleIdx? im.module then c := c ||| clo[j.toNat]!
    clo := clo.push c
  let mut alts : Std.HashMap Name (Array Nat) := {}
  for i in [0:mods.size] do
    for c in env.header.moduleData[i]!.constNames do
      if (env.getModuleIdxFor? c).map (·.toNat) != some i then
        alts := alts.insert c ((alts.getD c #[]).push i)
  let h ← IO.FS.Handle.mk out .write
  for i in [0:mods.size] do
    let data := env.header.moduleData[i]!
    let imps := data.imports.toList.map fun im =>
      im.module.toString ++ (if im.isExported then "+p" else "") ++ (if im.isMeta then "+m" else "")
    let line := s!"{mods[i]!}\t{",".intercalate imps}"
    unless (`VerifiedGarbage).isPrefixOf mods[i]! do
      h.putStrLn (line ++ "\t\t\t-")
      continue
    let byName : Std.HashMap Name ConstantInfo :=
      data.constants.foldl (fun m ci => m.insert ci.name ci) {}
    let modOf (c : Name) : Option Nat := do
      let j := (← env.getModuleIdxFor? c).toNat
      if clo[i]!.testBit j then return j
      (alts.getD c #[]).find? (clo[i]!.testBit ·)
    -- Everything the module's constants use.
    let mut all : Std.HashSet Nat := {}
    let mut isMeta := false
    for ci in data.constants do
      if let some hd := ci.type.getForallBody.getAppFn.constName? then
        if metaTypes.contains hd then isMeta := true
      for e in [ci.type] ++ ci.value?.toList do
        for c in e.getUsedConstants do
          if let some j := modOf c then
            if j != i then all := all.insert j
    -- The public surface, from every declaration that is not private.
    let mut pub : Std.HashSet Nat := {}
    let mut seen : Std.HashSet Name := {}
    let mut todo : Array Name := data.constants.filterMap fun ci =>
      if isPrivateName ci.name then none else some ci.name
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := byName[n]? | continue
      let es := match ci with
        | .thmInfo t => if isAux n then [t.type, t.value] else [t.type]
        | _ => [ci.type] ++ ci.value?.toList
      for e in es do
        for c in e.getUsedConstants do
          match modOf c with
          | some j => if j != i then pub := pub.insert j else todo := todo.push c
          | none => pure ()
    let names (s : Std.HashSet Nat) := ",".intercalate (s.toList.map (mods[·]!.toString))
    h.putStrLn s!"{line}\t{names pub}\t{names all}\t{if isMeta then "meta" else "-"}"
