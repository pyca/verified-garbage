module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.MacroArgUtil
public meta import Lean.Elab.Syntax

/-!
# `tactic_template`: tactic macros without elaborating their quotation

Untrusted: this only changes how a tactic macro's expansion is built, not
what it does.

`macro "foo" ts:simpLemma,* : tactic => `(tactic| simp only [a, b, $ts,*])`
elaborates its quotation as a term that builds the syntax: in a module with
many imports a second or more for a macro passing 50–100 lemma names to
`simp` (AES-CCM's `crun`: 20M heartbeats), in every module that defines one.
And the names it writes carry macro scopes, which `simp` elaborates an order
of magnitude slower than plain names, at every use (`plain_simp_names`).

`tactic_template "foo" ts:simpLemma,* : tactic => `(tactic| simp only [a, b, $ts,*])`
defines the same tactic without elaborating the quotation: it resolves each
name of the body to the constant it names where the template is defined,
keeps the body as text, and at each use parses that text and substitutes the
arguments (`$x` and the splices `$x,*`, `$x*`). The names it writes are plain
constants, so `simp` elaborates them fast.

Unlike a macro it is not hygienic: a name of the body that is not a global
constant where the template is defined (a hypothesis `h`, a binder) is
resolved where it is used, so a hypothesis of the caller with that name is
the one the body means.
-/

public meta section

namespace VG.TacticTemplate

open Lean Elab Command Tactic

/-- The variable of the antiquotation `stx` (`$x`, or `$x:cat`), if it is one. -/
def antiquotVar? (stx : Syntax) : Option Name :=
  if stx.isAntiquots then
    let t := stx.getCanonicalAntiquot.getAntiquotTerm
    if t.isIdent then some t.getId else none
  else none

/-- `stx` with every source position replaced by `info`, so that errors
in the template's expansion are reported where it is used. -/
partial def setInfo (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (setInfo info))
  | .atom _ v => .atom info v
  | .ident _ raw n pre => .ident info raw n pre
  | .missing => .missing

/-- `stx` with its antiquotations replaced by the syntax `arg` gives their
variables: `$x` by the argument, a splice `$x,*` or `$x*` by the elements
(and separators) of the argument. An empty splice takes its separator with
it. -/
partial def subst (arg : Name → Option Syntax) (stx : Syntax) : Except String Syntax := do
  if let some x := antiquotVar? stx then
    let some v := arg x | throw s!"tactic_template: unknown variable `{x}`"
    return v
  match stx with
  | .node info k args =>
    let mut out : Array Syntax := #[]
    let mut dropSep := false
    for a in args do
      if a.isAntiquotSuffixSplice then
        let some x := antiquotVar? a.getAntiquotSuffixSpliceInner
          | throw "tactic_template: unsupported splice"
        let some v := arg x | throw s!"tactic_template: unknown variable `{x}`"
        if v.getArgs.isEmpty then
          -- The separator before the splice, or else the one after it.
          if out.back?.any (·.isAtom) then out := out.pop else dropSep := true
        else
          out := out ++ v.getArgs
      else if dropSep && a.isAtom then
        dropSep := false
      else
        out := out.push (← subst arg a)
    return .node info k out
  | _ => return stx

/-- Run the template `text` (the text of a quotation `` `(tactic| …) ``) on
the syntax `stx` of a use: the variable `x` of `vars` is argument `i` of
`stx`. -/
def run (text : String) (vars : Array (Name × Nat)) : Tactic := fun stx => do
  let q ← match Parser.runParserCategory (← getEnv) `term text "<tactic_template>" with
    | .ok q => pure q
    | .error e => throwError "tactic_template: {e}"
  let body := setInfo (SourceInfo.fromRef stx) q[1]
  let arg (x : Name) : Option Syntax := (vars.find? (·.1 == x)).map fun (_, i) => stx[i]
  match subst arg body with
  | .ok t => withRef stx <| evalTactic t
  | .error e => throwError e

/-- The names of `stx`, outside antiquotations, that name a single global
constant here (`resolveGlobalName`), with the byte range of each. -/
partial def globalNames (stx : Syntax) : CommandElabM (Array (String.Pos.Raw × String.Pos.Raw × Name)) := do
  if stx.isAntiquots || stx.isAntiquotSuffixSplice then return #[]
  match stx with
  | .ident _ _ n _ =>
    let some s := stx.getPos? | return #[]
    let some e := stx.getTailPos? | return #[]
    let env ← getEnv
    let cs := (← liftCoreM <| resolveGlobalName n).filter (·.2.isEmpty)
    let [(c, _)] := cs | return #[]
    if isPrivateName c || !env.contains c then return #[]
    return #[(s, e, c)]
  | .node _ _ args => args.foldlM (fun acc a => return acc ++ (← globalNames a)) #[]
  | _ => return #[]

/-- The source text of `stx` with each name of `names` written as the
constant it names. -/
def textOf (stx : Syntax) (names : Array (String.Pos.Raw × String.Pos.Raw × Name)) :
    CommandElabM String := do
  let src := (← getFileMap).source
  let some s := stx.getPos? | throwError "tactic_template: the body has no position"
  let some e := stx.getTailPos? | throwError "tactic_template: the body has no position"
  let mut out := ""
  let mut p := s
  for (a, b, c) in names.qsort (fun x y => x.1 < y.1) do
    out := out ++ String.Pos.Raw.extract src p a ++ (`_root_ ++ c).toString
    p := b
  return out ++ String.Pos.Raw.extract src p e

/-- `tactic_template "foo" x:cat … : tactic => `(tactic| …)`: the tactic
`macro` would define, built from the text of its body at each use instead
of elaborating the quotation (see the module's documentation). -/
syntax (name := tacticTemplate) (docComment)? "tactic_template " (Lean.Parser.Command.macroArg)* " : " ident
  " => " term : command

@[command_elab tacticTemplate] def elabTacticTemplate : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let args : Array (TSyntax ``Lean.Parser.Command.macroArg) := stx[2].getArgs.map (⟨·⟩)
  let cat : Ident := ⟨stx[4]⟩
  let rhs := stx[6]
  unless cat.getId == `tactic do throwErrorAt cat "tactic_template: only tactics"
  unless rhs.getKind == ``Lean.Parser.Tactic.quot do
    throwErrorAt rhs "tactic_template: the body must be a quotation `(tactic| …)"
  let stxParts ← args.mapM fun a => return (← expandMacroArg a).1
  let vars : Array (Name × Nat) := args.zipIdx.filterMap fun (a, i) =>
    -- `x:` (optional), then the syntax.
    if a.raw[0][0].isIdent then some (a.raw[0][0].getId, i) else none
  let kind ← elabSyntax (← `($[$doc?:docComment]? syntax $[$stxParts]* : tactic))
  let text ← textOf rhs (← globalNames rhs[1])
  let impl := mkIdent (`_root_ ++ kind ++ `template)
  elabCommand (← `(@[tactic $(mkIdent kind)] meta def $impl : Lean.Elab.Tactic.Tactic :=
    VG.TacticTemplate.run $(quote text) $(quote vars)))

end VG.TacticTemplate
