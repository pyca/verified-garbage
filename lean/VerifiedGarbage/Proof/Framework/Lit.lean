module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public import Lean.Elab.Tactic.Rewrite
public meta import Lean.Elab.Tactic.Rewrite
public import Lean.Meta.Eval
public meta import Lean.Meta.Eval
public import Lean.Util.ShareCommon
public meta import Lean.Util.ShareCommon
public import VerifiedGarbage.TCB.Code

/-!
# Code as literals, for the kernel

The kernel evaluates code (the constant-time analysis, `Artifact.spSafe`, and
checks of every instruction), and most of that time can go into building the
instruction lists, which the code builds with functions (`List.append`,
`flatMap`, the round functions...), each structurally recursive: more than
the checks themselves, and again in every module that evaluates the code.

`materialize_code foo` evaluates `foo` (in compiled code) and defines
`foo.lit`, the same code written out as a literal, and
`foo.lit_eq : foo = foo.lit`, which the kernel checks once, by evaluation.
A proof about `foo.lit` is then a proof about `foo`. Code that calls a
function already materialized (`.call n g` with `g.lit` defined) refers to
`g.lit` rather than repeating it, so the kernel checks the callee's
instructions once for every caller (in `g.lit_eq`).

`lit_decide` proves a goal by `decide +kernel` after rewriting the code in
it that has a literal (`rw_lit`); `taint_decide` does the same.
-/

@[expose] public section

namespace VG

deriving instance Lean.ToExpr for Code

open Lean Meta Elab Command

namespace Lit

/-- The functions `materialize_code` has materialized, whose literals the
literals of their callers refer to: each `N` with a theorem `N.lit_eq`, in the
modules of this project (`VerifiedGarbage…`) and the current one. They are
found by name rather than recorded in an environment extension, whose
`initialize` the emitter's audit refuses (`TCB/Audit.lean`). -/
meta def litNames (env : Environment) : Array Name := Id.run do
  let add (acc : Array Name) (n : Name) : Array Name :=
    match n with
    | .str p "lit_eq" => if env.contains (.str p "lit") then acc.push p else acc
    | _ => acc
  let mut out := #[]
  -- (`moduleNames` builds the array on every use.)
  let mods := env.header.moduleNames
  for h : i in [0:mods.size] do
    if mods[i].getRoot.toString.startsWith "VerifiedGarbage" then
      out := env.header.moduleData[i]!.constNames.foldl add out
  return env.constants.foldStage2 (fun acc n _ => add acc n) out

/-- Replaces each body of a call in `e` (a literal `Code`) that is the literal of a
materialized function by a free variable, returning the abstracted literal and the
functions, in the order of the free variables. Each distinct subterm is visited
once (with the calls in it replaced, in the state). -/
meta partial def abstractCalls (lits : Std.HashMap Expr Name) (e : Expr) :
    StateT (Std.HashMap Expr Expr × Array Name) MetaM Expr := do
  -- A block contains instructions, with no callee positions to abstract.
  if e.isAppOfArity ``Code.block 3 then return e
  match e with
  | .app f a =>
    if let some e' := (← get).1[e]? then return e'
    let e' ← match (if e.isAppOfArity ``Code.call 4 then lits[a]? else none) with
      | some g => do
        let gs := (← get).2
        let i := (gs.findIdx? (· == g)).getD gs.size
        if i == gs.size then modify fun (m, gs) => (m, gs.push g)
        pure (mkApp f (.bvar (1000000 + i)))
      | none => do
        let f' ← abstractCalls lits f
        let a' ← abstractCalls lits a
        pure (.app f' a')
    modify fun (m, gs) => (m.insert e e', gs)
    return e'
  | _ => return e

/-- The literal `g.lit` written out in full: with the literal of each
materialized function it calls (`h.lit`) replaced by its own, in turn. This is
the value of `g`, as `materialize` evaluated it. -/
meta partial def expandLit (g : Name) : StateT (Std.HashMap Name Expr) MetaM Expr := do
  if let some e := (← get)[g]? then return e
  let env ← getEnv
  let some v := (env.find? (g ++ `lit)).bind (·.value?)
    | throwError "materialize_code: {g ++ `lit} has no value"
  let mut sub : Std.HashMap Name Expr := {}
  for c in v.getUsedConstants do
    if let .str p "lit" := c then
      if env.contains (.str p "lit_eq") then
        sub := sub.insert c (← expandLit p)
  let e := if sub.isEmpty then v else
    v.replace fun x => match x with
      | .const c _ => sub[c]?
      | _ => none
  modify (·.insert g e)
  return e

/-- The code `lhs` of `N.lit_eq : lhs = N.lit`. -/
meta def lhsOf (N : Name) : MetaM Expr := do
  let some (_, lhs, _) := (← getConstInfo (N ++ `lit_eq)).type.eq?
    | throwError "{N ++ `lit_eq} is not an equation"
  return lhs

/-- The constants `c` with a literal (`c.lit_eq : c = c.lit`), from
`materialize_code c` or `materialize_table c`. -/
meta def litConsts (env : Environment) (names : Array Name := litNames env) : Array Name :=
  names.filter fun N => match env.find? (N ++ `lit_eq) with
    | some ci => match ci.type.eq? with
      | some (_, .const c _, _) => c == N
      | _ => false
    | none => false

/-- The constants `c` with a literal of another name (`N.lit_eq : c = N.lit`,
from `materialize_code N := c` or `materialize_value N := c`). -/
meta def litAliases (env : Environment) (names : Array Name := litNames env) : Array Name :=
  names.filterMap fun N => match env.find? (N ++ `lit_eq) with
    | some ci => match ci.type.eq? with
      | some (_, .const c _, _) => if c == N then none else some c
      | _ => none
    | none => none

/-- Whether `S` is a structure with a field that is a proof. -/
meta def hasProofFields (S : Expr) : MetaM Bool := do
  let .const S _ := S | return false
  let env ← getEnv
  unless isStructure env S do return false
  forallTelescopeReducing (getStructureCtor env S).type fun xs _ =>
    xs.anyM fun x => do isProp (← inferType x)

/-- Whether `c` is from a module that builds code (or the current module):
not the trusted base, the specifications or this framework, whose
definitions (the ISA models, ...) never lead to code with a literal, and
which `reaches` would otherwise search on every call. -/
meta def codeModule (env : Environment) (mods : Array Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i => match mods[i.toNat]?.map (·.components) with
    | some (`VerifiedGarbage :: `Proof :: `Framework :: _) => false
    | some (`VerifiedGarbage :: k :: _) => k ∈ [`Impl, `Proof, `Variants, `Generic, `Artifacts]
    | _ => false

/-- The index of the first module with one of `targets` (the number of
modules if they are all of the current one). A definition uses only
constants of its module and of the modules it imports, which come before it:
none of a module before that one leads to a target. -/
meta def firstModuleOf (env : Environment) (targets : NameSet) : Nat :=
  targets.foldl (init := env.header.moduleNames.size) fun i c =>
    match env.getModuleIdxFor? c with
    | some j => min i j.toNat
    | none => i

/-- Whether the definition `c` uses one of `targets`, directly or through
definitions of this project, memoized in the state; `first` is
`firstModuleOf targets`. -/
meta partial def reaches (targets : NameSet) (mods : Array Name) (first : Nat) (c : Name) :
    StateT (NameMap Bool) MetaM Bool := do
  if let some b := (← get).find? c then return b
  modify (·.insert c false)
  let env ← getEnv
  if let some i := env.getModuleIdxFor? c then
    if i.toNat < first then return false
  unless codeModule env mods c do return false
  let some (.defnInfo d) := env.find? c | return false
  -- Only data: unfolding a proposition could hide its `Decidable` instance.
  if d.type.getForallBody.isProp then return false
  let mut r := false
  -- Every constant used is visited (no early exit): `unfoldWhere` unfolds
  -- exactly the constants memoized as reaching, so stopping at the first one
  -- would leave the others (e.g. the second of two calls to code with a
  -- literal) folded, and the kernel would evaluate them again.
  for u in d.value.getUsedConstants do
    if targets.contains u then r := true
    else if u.getRoot == `VG && !(u matches .str _ "lit") then
      if ← reaches targets mods first u then r := true
  -- Rewriting code inside a structure with proofs about it would change the
  -- types of those proofs.
  if r then r := !(← hasProofFields d.type.getForallBody.getAppFn)
  modify (·.insert c r)
  return r

/-- `e` with the applications of the constants `p` holds of unfolded, again
in what they unfold to. A plain `Expr.replace`, which visits each shared
subterm once: the goals of `rw_lit` carry large literals (a hint of
`taint_decide`) that have nothing to unfold. -/
meta partial def unfoldWhere (env : Environment) (p : Name → Bool) (e : Expr)
    (stop : Expr → Bool := fun _ => false) : Expr :=
  e.replace fun t => if stop t then some t else match t.getAppFn with
    | .const c ls =>
      if p c then match env.find? c with
        | some (.defnInfo d) =>
          some (unfoldWhere env p ((d.value.instantiateLevelParams d.levelParams ls).betaRev
            t.getAppRevArgs) stop)
        | _ => none
      else none
    | _ => none

/-- The maximal closed subterms of `e` whose head is a definition that leads
to code with a literal (`reaches`), or one of them, given the names of the
literals (`litNames`): to a constant with a literal, its own or another's
(`materialize_value N := c`, which `unfoldToLits` rewrites as an atom), or
to the head of an application with one (`materialize_code M := f a`, a
template), as `unfoldToLits` unfolds to them. -/
meta def reachingSubterms (names : Array Name) (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let mods := (← getEnv).header.moduleNames
  let mut targets := (litConsts env names ++ litAliases env names).foldl (fun s c => s.insert c) ({} : NameSet)
  -- The heads of the code with a literal that is an application
  -- (`materialize_code M := f a`, a template): code that leads to one of
  -- them alone (a generic function of a curve's configuration, whose pieces
  -- have literals for that curve) is unfolded to them too.
  for M in names do
    let lhs ← lhsOf M
    if let .const c _ := lhs.getAppFn then
      if lhs.isApp && !lhs.hasLooseBVars && !targets.contains c && codeModule env mods c then
        if let some (.defnInfo _) := env.find? c then targets := targets.insert c
  if targets.isEmpty then return #[]
  let targets' := targets
  let first := firstModuleOf env targets'
  let mut memo : NameMap Bool := {}
  for u in e.getUsedConstants do
    if !targets'.contains u then
      (_, memo) ← (reaches targets' mods first u).run memo
  let memo' := memo
  let hit (c : Name) := targets'.contains c || memo'.find? c == some true
  unless e.getUsedConstants.any hit do return #[]
  let rec go (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
    if (← get).1.contains e then return
    modify fun (v, out) => (v.insert e, out)
    match e.getAppFn with
    | .const c _ =>
      if hit c && !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then
        modify fun (v, out) => (v, out.push e)
        return
    | _ => pure ()
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  let ((), (_, out)) := (go e).run ({}, #[])
  return out

/-- For `x` (code, or a goal), a proof of `x = x'` and `x'`, where `x'` is `x`
with the definitions that lead to constants with a literal (but `N`)
unfolded, and those constants replaced by their literals; `none` if `x`
reaches none. The kernel checks the unfolding by delta reduction alone, and
then, evaluating `x'`, reads each literal rather than running again the
functions it was evaluated from: functions that build code (a register
allocator, tables of constants) are evaluated once, in their own `lit_eq`,
rather than in every literal or check of the code that uses them. -/
meta def unfoldToLits (N : Name) (x : Expr) (names? : Option (Array Name) := none) :
    MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  let names := match names? with | some n => n | none => litNames env
  let targets := (litConsts env names).foldl (fun s c => if c == N then s else s.insert c) {}
  -- The code with a literal that is an application (`materialize_code M := f a`):
  -- its occurrences are rewritten to `M.lit` as a whole (and not unfolded), so
  -- the definitions that lead to `f` are unfolded too.
  let mut atoms : Array (Name × Expr) := #[]
  for M in names do
    if M == N || targets.contains M then continue
    let lhs ← lhsOf M
    if lhs.getAppFn.isConst && !lhs.hasLooseBVars && !lhs.hasFVar && !lhs.hasMVar then
      atoms := atoms.push (M, lhs)
  let heads := atoms.foldl (fun s (_, l) => s.insert l.getAppFn.constName!) ({} : NameSet)
  let reachT := heads.foldl (fun s c => s.insert c) targets
  if reachT.isEmpty then return none
  let consts := x.getUsedConstants
  let mods := env.header.moduleNames
  let first := firstModuleOf env reachT
  let mut memo : NameMap Bool := {}
  for u in consts do
    if !reachT.contains u then
      (_, memo) ← (reaches reachT mods first u).run memo
  unless memo.any (fun _ b => b) || consts.any reachT.contains do return none
  -- The heads of the applications are unfolded where they are not one of
  -- them, if they lead to constants with a literal (or other applications).
  let mut headReach : NameSet := {}
  for c in heads do
    let some (.defnInfo d) := env.find? c | continue
    if !codeModule env mods c || d.type.getForallBody.isProp then continue
    let mut r := false
    for v in d.value.getUsedConstants do
      if reachT.contains v then r := true
      else if v.getRoot == `VG && !(v matches .str _ "lit") then
        let (b, m) ← (reaches reachT mods first v).run memo
        memo := m
        if b then r := true
    if r && !(← hasProofFields d.type.getForallBody.getAppFn) then headReach := headReach.insert c
  let memo' := memo
  let headReach' := headReach
  -- The templates (`materialize_template`): their applications are found up to
  -- definitional equality of the fixed arguments, and are not unfolded either.
  let tpls ← atoms.filterM fun (_, l) => do return (← whnfD (← inferType l)).isForall
  let isTplApp (l t : Expr) : Bool := t.getAppFn == l.getAppFn && t.getAppNumArgs == l.getAppNumArgs
  let isAtom (t : Expr) : Bool :=
    t.getAppFn.isConst && heads.contains t.getAppFn.constName! &&
      (atoms.any (·.2 == t) || tpls.any fun (_, l) => isTplApp l t)
  let e := unfoldWhere env (fun c => memo'.find? c == some true || headReach'.contains c) x isAtom
  -- What is rewritten to a literal: the constants with one, then the applications.
  let mut items : Array (Expr × Name) :=
    (e.getUsedConstants.filter targets.contains).map fun c => (mkConst c, c)
  for (M, lhs) in atoms do
    if (e.find? (· == lhs)).isSome then items := items.push (lhs, M)
  let mut argEq : Std.HashMap (Expr × Expr) Bool := {}
  for (M, lhs) in tpls do
    let found ← IO.mkRef (#[] : Array Expr)
    e.forEach fun t => do
      if isTplApp lhs t && t != lhs && !t.hasLooseBVars then found.modify (·.push t)
    for t in ← found.get do
      if items.any (·.1 == t) then continue
      -- By the kernel's check (as the proof will be), which decides closed terms
      -- (moduli, offsets) by evaluation, faster than `isDefEq`; of the arguments,
      -- since the kernel unfolds the two applications where an argument differs
      -- and compares the code they build (0.4 s for a product of another modulus).
      let mut same := true
      for a in t.getAppArgs, b in lhs.getAppArgs do
        let eq ← match argEq[(a, b)]? with
          | some eq => pure eq
          | none => do
            let eq := a == b || Kernel.isDefEqGuarded (← getEnv) {} a b
            argEq := argEq.insert (a, b) eq
            pure eq
        unless eq do
          same := false
          break
      if same then items := items.push (t, M)
  if items.isEmpty then return none
  let ty ← inferType x
  let u ← getLevel ty
  let itemIdx (t : Expr) : Option Nat := items.findIdx? fun (pat, _) => match pat, t with
    | .const c _, .const c' _ => c == c'
    | pat, t => !pat.isConst && pat == t
  -- `e` with the `j`-th item replaced by its literal for `j < k`, and by `y`
  -- for `j = k`; later items are left as they are (and not looked into).
  let inst (k : Nat) (y : Option Expr) : Expr :=
    e.replace fun t => match itemIdx t with
      | some j => if j < k then some (mkConst (items[j]!.2 ++ `lit))
          else if j == k then y else some t
      | none => none
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [u]) ty x rhs
  -- `x = e` by delta, then each item rewritten to its literal.
  let mut prf := mkApp2 (mkConst ``Eq.refl [u]) ty x
  for h : k in [0:items.size] do
    let (pat, M) := items[k]
    let cty ← inferType pat
    let lvl ← getLevel cty
    let motive ← withLocalDeclD `y cty fun y => mkLambdaFVars #[y] (eqTy (inst k (some y)))
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive pat) (mkApp motive (mkConst (M ++ `lit)))
      (mkApp6 (mkConst ``congrArg [lvl, 1]) cty (mkSort 0) pat
        (mkConst (M ++ `lit)) motive (mkConst (M ++ `lit_eq))) prf
  return some (inst items.size none, prf)

/-! ### Code in terms the kernel evaluates cheaply

The kernel checks `N.lit_eq` by evaluating the code, and most of that is the
functions of core that build lists. Compiled from their equations to `brecOn`
and a matcher, `++` takes the kernel about 35 µs for each element it copies,
and code copies an instruction once for every `++` above it; by the recursor
(`appendK`) it takes 6. So `kernelTerm` gives for a closed term an equal one in
which those functions are the ones below (`kernelPrims`), `a ++ b ++ c` copies
each list once (`chain3`), and the arithmetic of `Nat` and the conditionals on
it are the functions the kernel computes with, not the notation's instances of
them. Each definition `c` of the project's code that reaches one of them, or of
core's lists and arrays (`kernelLooks`), is declared again, privately, over
the others declared so, with the proof that it is `c`: by congruence in the
constants that differ, which the kernel checks without evaluating anything. The
declarations serve the rest of the module. -/

section Kernel

section

/-! The functions of core, by the recursors. -/

variable {α β : Type}

noncomputable def appendK (a b : List α) : List α := List.rec b (fun x _ r => x :: r) a
noncomputable def mapK (f : α → β) (a : List α) : List β := List.rec [] (fun x _ r => f x :: r) a
noncomputable def flattenK (a : List (List α)) : List α := List.rec [] (fun x _ r => appendK x r) a
noncomputable def flatMapK (f : α → List β) (a : List α) : List β := List.rec [] (fun x _ r => appendK (f x) r) a
noncomputable def filterMapK (f : α → Option β) (a : List α) : List β :=
  List.rec [] (fun x _ r => Option.rec r (fun y => y :: r) (f x)) a
noncomputable def filterK (p : α → Bool) (a : List α) : List α :=
  List.rec [] (fun x _ r => Bool.rec r (x :: r) (p x)) a
noncomputable def anyK (a : List α) (p : α → Bool) : Bool := List.rec false (fun x _ r => Bool.rec r true (p x)) a
noncomputable def allK (a : List α) (p : α → Bool) : Bool := List.rec true (fun x _ r => Bool.rec false r (p x)) a
noncomputable def foldlK (f : α → β → α) (z : α) (a : List β) : α :=
  List.rec (motive := fun _ => α → α) (fun z => z) (fun x _ r z => r (f z x)) a z
noncomputable def foldrK (f : α → β → β) (z : β) (a : List α) : β := List.rec z (fun x _ r => f x r) a
noncomputable def reverseAuxK (a b : List α) : List α :=
  List.rec (motive := fun _ => List α → List α) (fun b => b) (fun x _ r b => r (x :: b)) a b
noncomputable def concatK (a : List α) (y : α) : List α := List.rec [y] (fun x _ r => x :: r) a
noncomputable def getOptK (a : List α) (i : Nat) : Option α :=
  List.rec (motive := fun _ => Nat → Option α) (fun _ => none)
    (fun x _ r i => Nat.rec (some x) (fun j _ => r j) i) a i
noncomputable def getK (a : List α) (i : Fin a.length) : α :=
  List.rec (motive := fun a => (i : Nat) → i < a.length → α) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun x _ r i => Nat.rec (motive := fun i => i < _ → α) (fun _ => x) (fun j _ h => r j (Nat.lt_of_succ_lt_succ h)) i) a i.1 i.2
noncomputable def takeK (n : Nat) (a : List α) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun x _ r n => Nat.rec [] (fun m _ => x :: r m) n) a n
noncomputable def dropK (n : Nat) (a : List α) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun x t r n => Nat.rec (x :: t) (fun m _ => r m) n) a n
noncomputable def setK (a : List α) (i : Nat) (y : α) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun x t r i => Nat.rec (y :: t) (fun j _ => x :: r j) i) a i
noncomputable def replicateK (n : Nat) (x : α) : List α := Nat.rec [] (fun _ r => x :: r) n
noncomputable def zipIdxK (a : List α) (n : Nat) : List (α × Nat) :=
  List.rec (motive := fun _ => Nat → List (α × Nat)) (fun _ => []) (fun x _ r n => (x, n) :: r (Nat.add n 1)) a n
noncomputable def rangeLoopK (n : Nat) (a : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun a => a) (fun m r a => r (m :: a)) n a
end

/-! Each is the function it is for. -/

theorem appendK_eq : @List.append.{0} = @appendK := by
  funext α a b; induction a with | nil => rfl | cons x a ih => exact congrArg (List.cons x) ih
theorem mapK_eq : @List.map.{0, 0} = @mapK := by
  funext α β f a; induction a with | nil => rfl | cons x a ih => exact congrArg (List.cons (f x)) ih
theorem flattenK_eq : @List.flatten.{0} = @flattenK := by
  funext α a; induction a with
  | nil => rfl
  | cons x a ih => rw [List.flatten_cons, ih]; exact congrFun (congrFun (congrFun appendK_eq α) x) _
theorem flatMapK_eq : @List.flatMap.{0, 0} = @flatMapK := by
  funext α β f a; induction a with
  | nil => rfl
  | cons x a ih => rw [List.flatMap_cons, ih]; exact congrFun (congrFun (congrFun appendK_eq β) (f x)) _
theorem append_appendK {α : Type} (a b : List α) : a ++ b = appendK a b :=
  congrFun (congrFun (congrFun appendK_eq α) a) b

/-! `a ++ b ++ …`, which copies `a` again for every `++`, as `++` associates. -/

def chain3 (α : Type) (a b c : List α) : List α := a ++ b ++ c
noncomputable def chain3K (α : Type) (a b c : List α) : List α :=
  appendK a (appendK b c)
theorem chain3K_eq : chain3 = chain3K := by
  funext α a b c; simp only [chain3, chain3K, ← append_appendK, List.append_assoc]
def chain4 (α : Type) (a b c d : List α) : List α := a ++ b ++ c ++ d
noncomputable def chain4K (α : Type) (a b c d : List α) : List α :=
  appendK a (appendK b (appendK c d))
theorem chain4K_eq : chain4 = chain4K := by
  funext α a b c d; simp only [chain4, chain4K, ← append_appendK, List.append_assoc]
def chain5 (α : Type) (a b c d e : List α) : List α := a ++ b ++ c ++ d ++ e
noncomputable def chain5K (α : Type) (a b c d e : List α) : List α :=
  appendK a (appendK b (appendK c (appendK d e)))
theorem chain5K_eq : chain5 = chain5K := by
  funext α a b c d e; simp only [chain5, chain5K, ← append_appendK, List.append_assoc]
def chain6 (α : Type) (a b c d e f : List α) : List α := a ++ b ++ c ++ d ++ e ++ f
noncomputable def chain6K (α : Type) (a b c d e f : List α) : List α :=
  appendK a (appendK b (appendK c (appendK d (appendK e f))))
theorem chain6K_eq : chain6 = chain6K := by
  funext α a b c d e f; simp only [chain6, chain6K, ← append_appendK, List.append_assoc]
def chain7 (α : Type) (a b c d e f g : List α) : List α := a ++ b ++ c ++ d ++ e ++ f ++ g
noncomputable def chain7K (α : Type) (a b c d e f g : List α) : List α :=
  appendK a (appendK b (appendK c (appendK d (appendK e (appendK f g)))))
theorem chain7K_eq : chain7 = chain7K := by
  funext α a b c d e f g; simp only [chain7, chain7K, ← append_appendK, List.append_assoc]
def chain8 (α : Type) (a b c d e f g h : List α) : List α := a ++ b ++ c ++ d ++ e ++ f ++ g ++ h
noncomputable def chain8K (α : Type) (a b c d e f g h : List α) : List α :=
  appendK a (appendK b (appendK c (appendK d (appendK e (appendK f (appendK g h))))))
theorem chain8K_eq : chain8 = chain8K := by
  funext α a b c d e f g h; simp only [chain8, chain8K, ← append_appendK, List.append_assoc]
theorem filterMapK_eq : @List.filterMap.{0, 0} = @filterMapK := by
  funext α β f a; induction a with
  | nil => rfl
  | cons x a ih => rw [List.filterMap_cons, ih]; simp only [filterMapK]; split <;> simp_all
theorem filterK_eq : @List.filter.{0} = @filterK := by
  funext α p a; induction a with
  | nil => rfl
  | cons x a ih => rw [List.filter_cons, ih]; simp only [filterK]; cases p x <;> rfl
theorem anyK_eq : @List.any.{0} = @anyK := by
  funext α a p; induction a with
  | nil => rfl
  | cons x a ih => rw [List.any_cons, ih]; simp only [anyK]; cases p x <;> rfl
theorem allK_eq : @List.all.{0} = @allK := by
  funext α a p; induction a with
  | nil => rfl
  | cons x a ih => rw [List.all_cons, ih]; simp only [allK]; cases p x <;> rfl
theorem foldlK_eq : @List.foldl.{0, 0} = @foldlK := by
  funext α β f z a; induction a generalizing z with | nil => rfl | cons x a ih => exact ih _
theorem foldrK_eq : @List.foldr.{0, 0} = @foldrK := by
  funext α β f z a; induction a with | nil => rfl | cons x a ih => exact congrArg (f x) ih
theorem reverseAuxK_eq : @List.reverseAux.{0} = @reverseAuxK := by
  funext α a b; induction a generalizing b with | nil => rfl | cons x a ih => exact ih _
theorem concatK_eq : @List.concat.{0} = @concatK := by
  funext α a y; induction a with | nil => rfl | cons x a ih => exact congrArg (List.cons x) ih
theorem getOptK_eq : @List.get?Internal.{0} = @getOptK := by
  funext α a i; induction a generalizing i with
  | nil => rfl
  | cons x a ih => cases i with | zero => rfl | succ i => exact ih i
theorem getK_eq : @List.get.{0} = @getK := by
  funext α a i; obtain ⟨i, h⟩ := i
  induction a generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x a ih => cases i with | zero => rfl | succ i => exact ih i _
theorem takeK_eq : @List.take.{0} = @takeK := by
  funext α n a; induction a generalizing n with
  | nil => cases n <;> rfl
  | cons x a ih => cases n with | zero => rfl | succ n => exact congrArg (List.cons x) (ih n)
theorem dropK_eq : @List.drop.{0} = @dropK := by
  funext α n a; induction a generalizing n with
  | nil => cases n <;> rfl
  | cons x a ih => cases n with | zero => rfl | succ n => exact ih n
theorem setK_eq : @List.set.{0} = @setK := by
  funext α a i y; induction a generalizing i with
  | nil => rfl
  | cons x a ih => cases i with | zero => rfl | succ i => exact congrArg (List.cons x) (ih i)
theorem replicateK_eq : @List.replicate.{0} = @replicateK := by
  funext α n x; induction n with | zero => rfl | succ n ih => exact congrArg (List.cons x) ih
theorem zipIdxK_eq : @List.zipIdx.{0} = @zipIdxK := by
  funext α a n; induction a generalizing n with
  | nil => rfl
  | cons x a ih => exact congrArg (List.cons (x, n)) (ih _)
theorem rangeLoopK_eq : @List.range.loop = @rangeLoopK := by
  funext n a; induction n generalizing a with | zero => rfl | succ n ih => exact ih _

/-! Conditionals on the comparison of `Nat`s, and on a `Bool`. -/

def iteEq (α : Type) (a b : Nat) (x y : α) : α := ite (a = b) x y
def iteLt (α : Type) (a b : Nat) (x y : α) : α := ite (a < b) x y
def iteLe (α : Type) (a b : Nat) (x y : α) : α := ite (a ≤ b) x y
def decideEq (a b : Nat) : Bool := decide (a = b)
def decideLt (a b : Nat) : Bool := decide (a < b)
def decideLe (a b : Nat) : Bool := decide (a ≤ b)
noncomputable def iteEqK (α : Type) (a b : Nat) (x y : α) : α := Bool.rec y x (Nat.beq a b)
noncomputable def iteLtK (α : Type) (a b : Nat) (x y : α) : α := Bool.rec y x (Nat.ble (Nat.succ a) b)
noncomputable def iteLeK (α : Type) (a b : Nat) (x y : α) : α := Bool.rec y x (Nat.ble a b)
theorem decideEq_eq : decideEq = Nat.beq := by
  funext a b; show Nat.beq a b = _; rfl
def ltK (a b : Nat) : Bool := Nat.ble (Nat.succ a) b
theorem decideLt_eq : decideLt = ltK := by
  funext a b; rfl
theorem decideLe_eq : decideLe = Nat.ble := by
  funext a b; rfl
theorem iteEqK_eq : iteEq = iteEqK := by
  funext α a b x y
  show ite (a = b) x y = Bool.rec y x (decideEq a b)
  simp only [decideEq]
  by_cases h : a = b <;> simp [h]
theorem iteLtK_eq : iteLt = iteLtK := by
  funext α a b x y
  show ite (a < b) x y = Bool.rec y x (decideLt a b)
  simp only [decideLt]
  by_cases h : a < b <;> simp [h]
theorem iteLeK_eq : iteLe = iteLeK := by
  funext α a b x y
  show ite (a ≤ b) x y = Bool.rec y x (decideLe a b)
  simp only [decideLe]
  by_cases h : a ≤ b <;> simp [h]

def diteEq (α : Type) (a b : Nat) (x : a = b → α) (y : ¬a = b → α) : α := dite (a = b) x y
noncomputable def diteEqK (α : Type) (a b : Nat) (x : a = b → α) (y : ¬a = b → α) : α :=
  Bool.rec (motive := fun c => Nat.beq a b = c → α) (fun h => y (Nat.ne_of_beq_eq_false h))
    (fun h => x (Nat.eq_of_beq_eq_true h)) (Nat.beq a b) rfl
theorem diteEqK_eq : diteEq = diteEqK := by
  funext α a b x y
  have key (c : Bool) (hc : Nat.beq a b = c) : diteEq α a b x y =
      Bool.rec (motive := fun c => Nat.beq a b = c → α) (fun h => y (Nat.ne_of_beq_eq_false h))
        (fun h => x (Nat.eq_of_beq_eq_true h)) c hc := by
    cases c with
    | true => exact dite_eq_left (Nat.eq_of_beq_eq_true hc)
    | false => exact dite_eq_right (Nat.ne_of_beq_eq_false hc)
  exact key _ rfl
def beqNat (a b : Nat) : Bool := a == b
theorem beqNat_eq : beqNat = Nat.beq := by
  funext a b; show decide (a = b) = _; exact congrFun (congrFun decideEq_eq a) b
def iteBool (α : Type) (c : Bool) (x y : α) : α := ite (c = true) x y
noncomputable def iteBoolK (α : Type) (c : Bool) (x y : α) : α := Bool.rec y x c
theorem iteBoolK_eq : iteBool = iteBoolK := by
  funext α c x y; cases c <;> rfl
noncomputable def andK (a b : Bool) : Bool := Bool.rec false b a
noncomputable def orK (a b : Bool) : Bool := Bool.rec b true a
theorem andK_eq : and = andK := by funext a b; cases a <;> rfl
theorem orK_eq : or = orK := by funext a b; cases a <;> rfl

/-- The functions of core (and of the notations above) with one for the
kernel, and the proof that it is the same. -/
meta def kernelPrims : List (Name × Name × Name) :=
  [(``List.append, ``appendK, ``appendK_eq), (``chain3, ``chain3K, ``chain3K_eq),
    (``chain4, ``chain4K, ``chain4K_eq), (``chain5, ``chain5K, ``chain5K_eq),
    (``chain6, ``chain6K, ``chain6K_eq), (``chain7, ``chain7K, ``chain7K_eq),
    (``chain8, ``chain8K, ``chain8K_eq), (``List.map, ``mapK, ``mapK_eq),
    (``List.flatten, ``flattenK, ``flattenK_eq), (``List.flatMap, ``flatMapK, ``flatMapK_eq),
    (``List.filterMap, ``filterMapK, ``filterMapK_eq), (``List.filter, ``filterK, ``filterK_eq),
    (``List.any, ``anyK, ``anyK_eq), (``List.all, ``allK, ``allK_eq),
    (``List.foldl, ``foldlK, ``foldlK_eq), (``List.foldr, ``foldrK, ``foldrK_eq),
    (``List.reverseAux, ``reverseAuxK, ``reverseAuxK_eq), (``List.concat, ``concatK, ``concatK_eq),
    (``List.get?Internal, ``getOptK, ``getOptK_eq),
    (``List.get, ``getK, ``getK_eq), (``List.take, ``takeK, ``takeK_eq), (``List.drop, ``dropK, ``dropK_eq),
    (``List.set, ``setK, ``setK_eq), (``List.replicate, ``replicateK, ``replicateK_eq),
    (``List.zipIdx, ``zipIdxK, ``zipIdxK_eq), (``List.range.loop, ``rangeLoopK, ``rangeLoopK_eq),
    (``diteEq, ``diteEqK, ``diteEqK_eq), (``iteEq, ``iteEqK, ``iteEqK_eq),
    (``iteLt, ``iteLtK, ``iteLtK_eq), (``iteLe, ``iteLeK, ``iteLeK_eq),
    (``iteBool, ``iteBoolK, ``iteBoolK_eq), (``decideEq, ``Nat.beq, ``decideEq_eq),
    (``decideLt, ``ltK, ``decideLt_eq), (``decideLe, ``Nat.ble, ``decideLe_eq),
    (``beqNat, ``Nat.beq, ``beqNat_eq), (``and, ``andK, ``andK_eq), (``or, ``orK, ``orK_eq)]

/-- The function of `Nat` the kernel computes with that a notation is. -/
meta def natOps : List (Name × Name) :=
  [(``HAdd.hAdd, ``Nat.add), (``HSub.hSub, ``Nat.sub), (``HMul.hMul, ``Nat.mul), (``HDiv.hDiv, ``Nat.div),
    (``HMod.hMod, ``Nat.mod), (``HPow.hPow, ``Nat.pow), (``HAnd.hAnd, ``Nat.land), (``HOr.hOr, ``Nat.lor),
    (``HXor.hXor, ``Nat.xor), (``HShiftLeft.hShiftLeft, ``Nat.shiftLeft),
    (``HShiftRight.hShiftRight, ``Nat.shiftRight)]

/-- The proposition of a comparison of `Nat`s, or that a `Bool` is true, and
its usual instance: which it is, and what it compares. -/
meta def comparison? (p inst : Expr) : Option (Name × Array Expr) :=
  let i := inst.getAppFn.constName?
  if p.isAppOfArity ``Eq 3 && (p.getArg! 0).isConstOf ``Nat && i == some ``instDecidableEqNat then
    some (``Eq, #[p.getArg! 1, p.getArg! 2])
  else if p.isAppOfArity ``LT.lt 4 && (p.getArg! 0).isConstOf ``Nat && i == some ``Nat.decLt then
    some (``LT.lt, #[p.getArg! 2, p.getArg! 3])
  else if p.isAppOfArity ``LE.le 4 && (p.getArg! 0).isConstOf ``Nat && i == some ``Nat.decLe then
    some (``LE.le, #[p.getArg! 2, p.getArg! 3])
  else if p.isAppOfArity ``Eq 3 && (p.getArg! 2).isConstOf ``Bool.true && i == some ``instDecidableEqBool then
    some (``Bool, #[p.getArg! 1])
  else none

/-- The type of the elements, if `e` is `a ++ b` for lists (of a `Type`). -/
meta def listAppend? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``HAppend.hAppend 6 then
    match e.getArg! 0, e.getArg! 3 with
    | .app (.const ``List [.zero]) α,
      .app (.app (.const ``instHAppendOfAppend _) _) (.app (.const ``List.instAppend _) _) => some α
    | _, _ => none
  else none

/-- `[a₁, …, aₙ]`, if `e` is `a₁ ++ … ++ aₙ` (before `bs`). -/
meta partial def spine (e : Expr) (bs : List Expr) : List Expr :=
  if (listAppend? e).isSome then spine (e.getArg! 4) (e.getArg! 5 :: bs) else e :: bs

/-- The functions for `++` of three lists, and more. -/
meta def chains : Array Name := #[``chain3, ``chain4, ``chain5, ``chain6, ``chain7, ``chain8]

/-- `e` with the notations in it replaced by the functions they stand for at
the instances they are at (`++` of lists, the arithmetic of `Nat`, a
conditional on a comparison of `Nat`s): the same term, by unfolding. -/
meta partial def unfoldNotation (e : Expr) : Expr :=
  e.replace fun t =>
    let f := t.getAppFn
    let arg (i : Nat) := unfoldNotation (t.getArg! i)
    -- An operand, as the numeral itself.
    let num (i : Nat) : Expr :=
      let a := t.getArg! i
      if a.isAppOfArity ``OfNat.ofNat 3 && (a.getArg! 0).isConstOf ``Nat && (a.getArg! 1).isRawNatLit then a.getArg! 1
      else unfoldNotation a
    match f, t.getAppNumArgs with
    | .const ``HAppend.hAppend _, 6 => do
      let α ← listAppend? t
      let l := spine t []
      if l.length < 3 then none
      let α := unfoldNotation α
      let l := l.map unfoldNotation
      -- Seven at a time, the first those before them.
      let rec go (a : Expr) (bs : List Expr) (fuel : Nat) : Expr :=
        match bs, fuel with
        | [], _ | _, 0 => a
        | [b], _ => mkApp3 (mkConst ``List.append [.zero]) α a b
        | bs, fuel + 1 => go (mkAppN (mkConst (chains[(bs.take 7).length - 2]!)) (#[α, a] ++ (bs.take 7).toArray)) (bs.drop 7) fuel
      return go l.head! l.tail! l.length
    | .const ``HAppend.hAppend _, 4 =>
      match t.getArg! 0, t.getArg! 3 with
      | .app (.const ``List [.zero]) α,
        .app (.app (.const ``instHAppendOfAppend _) _) (.app (.const ``List.instAppend _) _) =>
        some (mkApp (mkConst ``List.append [.zero]) (unfoldNotation α))
      | _, _ => none
    | .const ``BEq.beq _, 2 =>
      if (t.getArg! 0).isConstOf ``Nat && (t.getArg! 1).isAppOf ``instBEqOfDecidableEq then some (mkConst ``beqNat)
      else none
    | .const ``ite [.succ .zero], 5 =>
      (comparison? (t.getArg! 1) (t.getArg! 2)).map fun (c, as) =>
        let g := if c == ``Eq then ``iteEq else if c == ``LT.lt then ``iteLt else if c == ``LE.le then ``iteLe
          else ``iteBool
        mkAppN (mkConst g) (#[arg 0] ++ as.map unfoldNotation ++ #[arg 3, arg 4])
    | .const ``dite [.succ .zero], 5 =>
      match comparison? (t.getArg! 1) (t.getArg! 2) with
      | some (``Eq, as) => some (mkAppN (mkConst ``diteEq) (#[arg 0] ++ as.map unfoldNotation ++ #[arg 3, arg 4]))
      | _ => none
    | .const ``Decidable.decide _, 2 =>
      match comparison? (t.getArg! 0) (t.getArg! 1) with
      | some (``Eq, as) => some (mkAppN (mkConst ``decideEq) (as.map unfoldNotation))
      | some (``LT.lt, as) => some (mkAppN (mkConst ``decideLt) (as.map unfoldNotation))
      | some (``LE.le, as) => some (mkAppN (mkConst ``decideLe) (as.map unfoldNotation))
      | _ => none
    | .const c _, 6 =>
      if (t.getArg! 0).isConstOf ``Nat && (t.getArg! 1).isConstOf ``Nat then
        (natOps.lookup c).map fun g => mkApp2 (mkConst g) (num 4) (num 5)
      else none
    | _, _ => none

/-- Whether `kernelTerm` looks for the functions of `kernelPrims` in `c`: the
project's code, and core's functions of lists and arrays (not of numbers,
which the kernel computes with). -/
meta def kernelLooks (env : Environment) (mods : Array Name) (c : Name) : Bool :=
  if c.getRoot ∈ [`List, `Array, `Vector, `Option, `Id, `Fin, `Prod] then true else codeModule env mods c

/-- The constants in `e`, with their levels. -/
meta def constsOf (e : Expr) : MetaM (Array Expr) := do
  let found ← IO.mkRef (({}, #[]) : Std.HashSet Expr × Array Expr)
  e.forEach fun t => do
    if t.isConst then
      found.modify fun (s, out) => if s.contains t then (s, out) else (s.insert t, out.push t)
  return (← found.get).2

/-- What `kernelTerm` has found for each constant: the constant to use in its
place and the proof that they are equal, or none. -/
meta abbrev KernelM := StateT (Std.HashMap Expr (Option (Expr × Expr))) MetaM

/-- `x`, which makes declarations, or `r` without them if the kernel rejects one. -/
meta def declareOr {α : Type} (r : α) (x : MetaM α) : MetaM α := do
  let env ← getEnv
  try withOptions (Elab.async.set · false) x
  catch _ =>
    setEnv env
    return r

mutual

/-- For a closed term `e`, the term with the constants that `kernelConst` has
another for replaced by it, and a proof that they are equal; none if it has
none of them. -/
meta partial def kernelTerm (look : Name → Bool) (e : Expr) : KernelM (Option (Expr × Expr)) := do
  let e₁ := unfoldNotation e
  let mut items : Array (Expr × Expr × Expr) := #[]
  for c in ← constsOf e₁ do
    if let some it ← kernelConst look c then items := items.push (c, it)
  if items.isEmpty then return none
  let k := items.size
  let idx : Std.HashMap Expr Nat := items.zipIdx.foldl (fun m ((c, _), i) => m.insert c i) {}
  let put (f : Nat → Expr) : Expr := e₁.replace fun t => if t.isConst then idx[t]?.map f else none
  let tys ← items.mapM fun (c, _, _) => inferType c
  -- `e` as a function of the constants, at them: `e` (by unfolding the notations).
  let xs ← (Array.range k).mapM fun _ => mkFVar <$> mkFreshFVarId
  let F := tys.foldr (fun ty b => Expr.lam `x ty b .default) ((put (xs[·]!)).abstract xs)
  let ety ← inferType e
  let u ← getLevel ety
  let mut l := F
  let mut r := F
  let mut prf := mkApp2 (mkConst ``Eq.refl [u]) ety e
  for i in [0:k] do
    let (c, c', p) := items[i]!
    -- The type of the function of the constants after this one.
    let B := (tys.extract (i + 1) k).foldr (fun ty b => mkForall `x .default ty b) ety
    let v ← getLevel tys[i]!
    let w ← getLevel B
    prf := if i == 0 then mkApp6 (mkConst ``congrArg [v, w]) tys[i]! B c c' F p
      else mkAppN (mkConst ``congr [v, w]) #[tys[i]!, B, l, r, c, c', prf, p]
    l := mkApp l c
    r := mkApp r c'
  return some (put fun i => (items[i]!).2.1, prf)

/-- The constant to use in place of the constant `c`, and the proof that they
are equal. -/
meta partial def kernelConst (look : Name → Bool) (c : Expr) : KernelM (Option (Expr × Expr)) := do
  if let some r := (← get)[c]? then return r
  modify (·.insert c none)
  let .const n ls := c | return none
  let r ← do
    if let some (_, c', p) := kernelPrims.find? (·.1 == n) then
      pure (if ls.all (· == .zero) then some (mkConst c', mkConst p) else none)
    else
      let env ← getEnv
      if n matches .str _ "lit" then return none
      unless look n do return none
      let N := mkPrivateName env (ls.foldl (fun N l => N.str (toString l)) (`VG.Lit.kernel ++ n))
      if env.contains N then pure (some (mkConst N, mkConst (N ++ `eq)))
      else
        let some (.defnInfo d) := env.find? n | return none
        if d.type.getForallBody.isProp || ls.any (·.hasParam) then return none
        -- (Code in a structure with proofs about it: the proofs are of the code as it is.)
        if ← hasProofFields d.type.getForallBody.getAppFn then return none
        let type := d.type.instantiateLevelParams d.levelParams ls
        let some (v, p) ← kernelTerm look (d.value.instantiateLevelParams d.levelParams ls) | return none
        declareOr none do
          addDecl <| .defnDecl { d with name := N, levelParams := [], type, value := v, all := [N] }
          addDecl <| .thmDecl {
            name := N ++ `eq, levelParams := [], value := p
            type := mkApp3 (mkConst ``Eq [← getLevel type]) type c (mkConst N) }
          return some (mkConst N, mkConst (N ++ `eq))
  modify (·.insert c r)
  return r

end

/-- `kernelTerm` of `e : ty`, leaving the constants `stop` as they are, or `e` itself
where there is none. The proof is a theorem named after `N`. -/
meta def forKernel (N : Name) (ty e : Expr) (stop : Array Name := #[]) : MetaM (Expr × Expr) := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let u ← getLevel ty
  let refl := (e, mkApp2 (mkConst ``Eq.refl [u]) ty e)
  let some (e', q) ← (kernelTerm (fun c => kernelLooks env mods c && !stop.contains c) e).run' {}
    | return refl
  let name := mkPrivateName env (N ++ `kernel_eq)
  if ← declareOr false do
    addDecl <| .thmDecl { name, levelParams := [], type := mkApp3 (mkConst ``Eq [u]) ty e e', value := q }
    return true
  then return (e', mkConst name)
  else return refl

/-- For `v : ty` closed, `v` with the literals it reaches (`unfoldToLits`) as the
kernel evaluates it cheaply (`kernelTerm`), and a proof that they are equal. -/
meta def litTerm (N : Name) (ty v : Expr) : MetaM (Expr × Expr) := do
  let (e, prf) ← match ← unfoldToLits N v with
    | some r => pure r
    | none => pure (v, mkApp2 (mkConst ``Eq.refl [1]) ty v)
  let (e', q) ← forKernel N ty e
  return (e', mkApp6 (mkConst ``Eq.trans [1]) ty v e e' prf q)

/-- A proof of `v = N.lit`, for `v : ty` closed, which the kernel checks by
evaluating `litTerm` of `v`. -/
meta def litProof (N : Name) (ty v : Expr) : MetaM Expr := (·.2) <$> litTerm N ty v

end Kernel

/-! ### Templates

Code built by a function of a few offsets (`mulG M o a b`, a product of the
operands at `a` and `b` into `o`) is evaluated by the kernel once for each
call, in every literal of the code that calls it: P-384's ECDH evaluates over
a hundred products. `materialize_template N := f x₁ … xₖ`, for
`f x₁ … xₖ : Nat → … → Nat → α`, evaluates it once instead, with the offsets
variables: `N.lit` is a function whose body is the code with each offset
`oᵢ + c` written as such (found by evaluating the code at a few offsets far
apart and comparing them, `antiUnify`), and the kernel checks
`N.lit_eq : f x₁ … xₖ = N.lit` with the offsets free. A literal of code that
calls it then evaluates `N.lit o a b`, the body with the offsets added
(`unfoldToLits`), rather than `f`.

The function must not decide anything on its offsets (the kernel could not
decide it with them free): give a name to the code of each case
(`mulR`'s `mulG`), and a template to that. `unfoldToLits` rewrites the
applications of `f` whose fixed arguments are `x₁ … xₖ` up to definitional
equality (the modulus is reached by many paths: `p384.MP'`,
`(jwinCfg p384).M`, …). -/

/-- `(T, n)` if `e` is the literal `OfNat.ofNat T n _` (`ToExpr` of `Nat`
and of a nonnegative `Int`). -/
meta def natLitOf? (e : Expr) : Option (Expr × Nat) :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.appFn!.appArg! with
    | .lit (.natVal n) => some (e.appFn!.appFn!.appArg!, n)
    | _ => none
  else none

/-- The offsets a template is evaluated at: sample `j`'s offset `i` is
`2⁴⁰ (1 + j (i + 1)) + 2³⁶ i`, so that no two offsets differ by the same
amount in every sample. -/
meta def tplSamples (k : Nat) : Array (Array Nat) :=
  (Array.range 3).map fun j => (Array.range k).map fun i => 0x10000000000 * (1 + j * (i + 1)) + 0x1000000000 * i

/-- The value at the same place in the samples `es` of a template (of the
parameters `xs`), the same in each, but for each number that differs between
them, which is `xᵢ + c` for one `xᵢ` and `c < 2³²` in every sample. -/
meta partial def antiUnify (xs : Array Expr) (samples : Array (Array Nat)) (es : Array Expr) :
    StateT (Std.HashMap (Array Expr) Expr) MetaM Expr := do
  let e0 := es[0]!
  if es.all (· == e0) then return e0
  if let some r := (← get)[es]? then return r
  let r ← do
    if let some (T, _) := natLitOf? e0 then
      let ns := es.filterMap fun e => (natLitOf? e).map (·.2)
      unless ns.size == es.size do
        throwError "materialize_template: a number in one sample, not in another"
      let follows (i : Nat) : Option Nat := Id.run do
        let c : Int := (ns[0]! : Int) - samples[0]![i]!
        unless 0 ≤ c && c < 0x100000000 do return none
        for j in [1:ns.size] do
          unless (ns[j]! : Int) - samples[j]![i]! == c do return none
        return some c.toNat
      let some (i, c) := (List.range xs.size).findSome? fun i => (follows i).map (i, ·)
        | throwError "materialize_template: a number that follows no parameter: {ns}"
      let s := mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
        (mkApp2 (mkConst ``instHAdd [0]) (mkConst ``Nat) (mkConst ``instAddNat)) xs[i]! (mkNatLit c)
      if T.isConstOf ``Nat then pure s
      else if T.isConstOf ``Int then pure (mkApp (mkConst ``Int.ofNat) s)
      else throwError "materialize_template: a number of type {T}"
    else
      let f := e0.getAppFn
      let n := e0.getAppNumArgs
      unless e0.isApp && es.all fun e => e.getAppFn == f && e.getAppNumArgs == n do
        throwError "materialize_template: the samples differ in shape (does the code decide on its offsets?)"
      let mut args := #[]
      for i in [0:n] do
        args := args.push (← antiUnify xs samples (es.map (·.getArg! i)))
      pure (mkAppN f args)
  modify (·.insert es r)
  return r

/-- `materialize_template N := f`: `N.lit` and `N.lit_eq : f = N.lit`, for `f`
a function of offsets (`Nat`), as above. -/
meta def materializeTemplate (N : Name) (f : Expr) : MetaM Unit := do
  if f.hasMVar || f.hasFVar then throwError "materialize_template: {f} is not closed"
  let ty ← inferType f
  forallTelescopeReducing ty fun xs body => do
    if xs.isEmpty then throwError "materialize_template: {f} is not a function"
    for x in xs do
      unless (← whnfD (← inferType x)).isConstOf ``Nat do
        throwError "materialize_template: a parameter is not a number: {x}"
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) body)
    let samples := tplSamples xs.size
    let es ← samples.mapM fun s => unsafe evalExpr Expr (mkConst ``Expr)
      (mkApp3 (mkConst ``ToExpr.toExpr [0]) body inst (mkAppN f (Array.map mkNatLit s)))
    let (b, _) ← (antiUnify xs samples es).run {}
    addDecl (forceExpose := true) <| .defnDecl {
      name := N ++ `lit, levelParams := [], type := ty
      value := ← mkLambdaFVars xs (ShareCommon.shareCommon' b)
      hints := .abbrev, safety := .safe }
    let u ← getLevel ty
    addDecl <| .thmDecl {
      name := N ++ `lit_eq, levelParams := [],
      type := mkApp3 (mkConst ``Eq [u]) ty f (mkConst (N ++ `lit)),
      value := (← forKernel N ty f).2 }

/-- What `codeToExprUnsafe` has converted: code, instructions and conditions
(apart: one without arguments is a number, the same in both types), by the
address of the value, which `c` keeps alive. -/
meta structure CodeExprs where
  code : Std.HashMap USize Expr := {}
  instrs : Std.HashMap USize Expr := {}
  conds : Std.HashMap USize Expr := {}

/-- `toExpr c`, for `c : Code I C` evaluated, each part of `c` converted once
however often it occurs (`c` keeps as one object what it evaluated once, and
`ShareCommon` makes one of equal parts): written out, code has up to millions
of instructions, a few thousand of them distinct, since each call holds the
body of its callee. `toI` and `toC` are the `toExpr` of `I` and `C`, whose
values the types here do not say. -/
meta unsafe def codeToExprUnsafe (I C : Expr) (toI toC : NonScalar → Expr)
    (c : Code NonScalar NonScalar) : Expr :=
  go (ShareCommon.shareCommon' c) |>.run' {}
where
  instr (x : NonScalar) : StateM CodeExprs Expr := do
    let k := ptrAddrUnsafe x
    if let some e := (← get).instrs[k]? then return e
    let e := toI x
    modify fun s => { s with instrs := s.instrs.insert k e }
    return e
  cond (x : NonScalar) : StateM CodeExprs Expr := do
    let k := ptrAddrUnsafe x
    if let some e := (← get).conds[k]? then return e
    let e := toC x
    modify fun s => { s with conds := s.conds.insert k e }
    return e
  block (is : List NonScalar) : StateM CodeExprs Expr := do
    let mut e := mkApp (mkConst ``List.nil [.zero]) I
    let cons := mkApp (mkConst ``List.cons [.zero]) I
    for i in is.reverse do
      e := mkApp2 cons (← instr i) e
    return mkApp3 (mkConst ``Code.block) I C e
  go (c : Code NonScalar NonScalar) : StateM CodeExprs Expr := do
    let k := ptrAddrUnsafe c
    if let some e := (← get).code[k]? then return e
    let e ← match c with
      | .block is => block is
      | .seq a b => pure <| mkApp4 (mkConst ``Code.seq) I C (← go a) (← go b)
      | .ite b t e =>
        pure <| mkApp5 (mkConst ``Code.ite) I C (← cond b) (← go t) (← go e)
      | .loop b c => pure <| mkApp4 (mkConst ``Code.loop) I C (← go b) (← cond c)
      | .call n b => pure <| mkApp4 (mkConst ``Code.call) I C (mkStrLit n) (← go b)
      | .frame p b q =>
        pure <| mkApp5 (mkConst ``Code.frame) I C (← instr p) (← go b) (← instr q)
      | .icall i n b next =>
        pure <| mkApp6 (mkConst ``Code.icall) I C (← instr i) (mkStrLit n) (← go b) (← go next)
    modify fun s => { s with code := s.code.insert k e }
    return e

/-- The value of the closed code `code : Code I C`, evaluated in compiled code,
as a literal (`codeToExprUnsafe`). -/
meta def evalCode (I C code : Expr) : MetaM Expr := do
  let toE (T : Expr) : MetaM (NonScalar → Expr) := do
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) T)
    unsafe evalExpr (NonScalar → Expr) (← mkArrow T (mkConst ``Expr))
      (mkApp2 (mkConst ``ToExpr.toExpr [0]) T inst)
  let toI ← toE I
  let toC ← toE C
  let c ← unsafe evalExpr (Code NonScalar NonScalar) (mkApp2 (mkConst ``Code) I C) code
  return unsafe codeToExprUnsafe I C toI toC c

/-- `abstractCalls` of `v`, a literal of type `ty`, for the functions
materialized so far. -/
meta def abstractToLits (ty v : Expr) : MetaM (Expr × Array Name) := do
  -- The code materialized so far, written out in full.
  let mut lits : Std.HashMap Expr Name := {}
  let mut expanded : Std.HashMap Name Expr := {}
  for g in litNames (← getEnv) do
    if (← isDefEq (← inferType (← lhsOf g)) ty) then
      let (e, m) ← (expandLit g).run expanded
      expanded := m
      lits := lits.insertIfNew e g
  let (abs, (_, gs)) ← (abstractCalls lits v).run ({}, #[])
  return (abs, gs)

/-- Defines `N.lit`, the value of the closed code term `code` as a literal
(calling the literals of the code materialized so far), and
`N.lit_eq : code = N.lit`. -/
meta def materialize (N : Name) (code : Expr) : MetaM Unit := do
  let ty ← inferType code
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do
    throwError "materialize_code: {code} is not code: {ty}"
  let codeTy := mkApp2 (mkConst ``Code) (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!)
  let v ← evalCode codeTy.appFn!.appArg! codeTy.appArg! code
  let (abs, gs) ← abstractToLits ty v
  let lhss ← gs.mapM lhsOf
  -- `abs` with the `i`-th callee (marked `.bvar (1000000 + i)`) replaced by `f i`.
  let inst (f : Nat → Expr) : Expr :=
    abs.replace fun e => match e with
      | .bvar k => if 1000000 ≤ k then some (f (k - 1000000)) else none
      | _ => none
  let litV := ShareCommon.shareCommon' (inst fun i => mkConst (gs[i]! ++ `lit))
  addDecl (forceExpose := true) <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := litV
    hints := .abbrev, safety := .safe }
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [1]) ty code rhs
  -- If the code reaches literals: `code = e` by unfolding (`unfoldToLits`),
  -- `e = e'` for the kernel (`kernelTerm`), and `e' = N.lit` by evaluation.
  if let some (e, prf) ← unfoldToLits N code then
    let (e', q) ← forKernel N ty e
    addDecl <| .thmDecl {
      name := N ++ `lit_eq, levelParams := [], type := eqTy (mkConst (N ++ `lit)),
      value := ShareCommon.shareCommon' (mkApp6 (mkConst ``Eq.trans [1]) ty code e e' prf q) }
    return
  -- `code = code'` for the kernel, `code' = abs[callees]` by evaluation, then each
  -- callee rewritten to its literal. (The callees' code stays as it is, so that the
  -- kernel need not evaluate it.)
  let mut prf := (← forKernel N ty code (lhss.filterMap (·.getAppFn.constName?))).2
  for i in [0:gs.size] do
    -- The code with the literals of the first `i` callees, and `x` for the `i`-th.
    let motive := Expr.lam `x ty
      (eqTy ((inst fun j => if j < i then mkConst (gs[j]! ++ `lit)
        else if j == i then .bvar 0 else lhss[j]!))) .default
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive lhss[i]!) (mkApp motive (mkConst (gs[i]! ++ `lit)))
      (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) lhss[i]!
        (mkConst (gs[i]! ++ `lit)) motive (mkConst (gs[i]! ++ `lit_eq))) prf
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := eqTy (mkConst (N ++ `lit)),
    value := ShareCommon.shareCommon' prf }

end Lit

/-- A function on `Nat` is the table of its first values, falling back to
itself beyond them. -/
theorem Lit.table_eq {α : Type} (f : Nat → α) (n : Nat) (l : List α)
    (h : (List.range n).map f = l) : f = fun i => l.getD i (f i) := by
  funext i
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (l := List.range n) (by simpa using hi)]; rfl

/-- A function of two `Nat`s is the table of its first values, falling back
to itself beyond them. -/
theorem Lit.table2_eq {α : Type} (f : Nat → Nat → α) (n m : Nat) (l : List (List α))
    (h : (List.range n).map (fun i => (List.range m).map (f i)) = l) :
    f = fun i j => (l.getD i []).getD j (f i j) := by
  funext i j
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi, Option.map_some, Option.getD_some, List.getElem?_map]
    by_cases hj : j < m
    · rw [List.getElem?_range hj]; rfl
    · rw [List.getElem?_eq_none (by simpa using hj)]; rfl
  · rw [List.getElem?_eq_none (l := List.range n) (by simpa using hi)]; rfl

/-- A function to `Nat` is its first values packed in `w`-bit fields of one
number `N` (`M = 2 ^ w`), falling back to itself beyond them: the kernel
reads a value with two arithmetic operations, which it runs natively,
rather than walking a list. -/
theorem Lit.packed_eq (f : Nat → Nat) (n w M N : Nat)
    (h : (List.range n).all (fun i => Nat.beq (N >>> (w * i) % M) (f i)) = true) :
    f = fun i => cond (Nat.blt i n) (N >>> (w * i) % M) (f i) := by
  funext i
  cases hi : Nat.blt i n
  · rfl
  · have hi : i < n := Nat.blt_eq.mp hi
    exact (Nat.eq_of_beq_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))).symm

/-- `Lit.packed_eq` for a function of two `Nat`s, its values at `i < n`,
`j < m` in field `m i + j`. -/
theorem Lit.packed2_eq (f : Nat → Nat → Nat) (n m w M N : Nat)
    (h : (List.range n).all (fun i => (List.range m).all fun j =>
      Nat.beq (N >>> (w * (m * i + j)) % M) (f i j)) = true) :
    f = fun i j => cond (Nat.blt i n && Nat.blt j m) (N >>> (w * (m * i + j)) % M) (f i j) := by
  funext i j
  cases hi : Nat.blt i n <;> cases hj : Nat.blt j m
  · rfl
  · rfl
  · rfl
  · have hi : i < n := Nat.blt_eq.mp hi
    have hj : j < m := Nat.blt_eq.mp hj
    exact (Nat.eq_of_beq_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j
      (List.mem_range.mpr hj))).symm

open Lit in
/-- `materialize_table f n`, for a closed `f : Nat → α`, defines `f.lit`, the
table of the values `f 0`, …, `f (n - 1)` as literals (and `f i` beyond
them), and `f.lit_eq : f = f.lit`, which the kernel checks by evaluating
those `n` values once. The literals of code that calls `f` then read the
table (`materialize_code`). `materialize_table f n m`, for a closed
`f : Nat → Nat → α`, does the same with the table of the values `f i j`,
`i < n`, `j < m`. A table of `Nat`s is one number (`Lit.packed_eq`), which
the kernel reads in constant time; others are lists. -/
elab "materialize_table " id:ident n:num m:(num)? : command => liftTermElabM do
  let f ← realizeGlobalConstNoOverloadWithInfo id
  let fty ← whnfD (← inferType (mkConst f))
  let .forallE _ (.const ``Nat []) α _ := fty
    | throwError "materialize_table: {f} is not a function on `Nat`: {fty}"
  if α.hasLooseBVars then throwError "materialize_table: {f} is dependent"
  let nat := mkConst ``Nat
  let range (k : Nat) := mkApp (mkConst ``List.range) (mkNatLit k)
  -- The values of the table (the type of its rows, and the values of `g`), and
  -- the value of `g` at `i` (and `j`) from the table `l`, else `d`.
  let (β, rowTy, valsOf, lookup) ← match m with
    | none => pure (α, α,
        fun (g : Expr) => mkApp4 (mkConst ``List.map [0, 0]) nat α g (range n.getNat),
        fun (l i _ d : Expr) => mkApp4 (mkConst ``List.getD [0]) α l i d)
    | some m =>
      let .forallE _ (.const ``Nat []) β _ ← whnfD α
        | throwError "materialize_table: {f} is not a function of two `Nat`s: {fty}"
      if β.hasLooseBVars then throwError "materialize_table: {f} is dependent"
      let rowTy := mkApp (mkConst ``List [0]) β
      pure (β, rowTy,
        fun (g : Expr) => mkApp4 (mkConst ``List.map [0, 0]) nat rowTy
          (.lam `i nat (mkApp4 (mkConst ``List.map [0, 0]) nat β (mkApp g (.bvar 0)) (range m.getNat)) .default)
          (range n.getNat),
        fun (l i j d : Expr) => mkApp4 (mkConst ``List.getD [0]) β
          (mkApp4 (mkConst ``List.getD [0]) rowTy l i (mkApp (mkConst ``List.nil [0]) β)) j d)
  let listTy := mkApp (mkConst ``List [0]) rowTy
  -- A table of `Nat`s is packed in one number (`Lit.packed_eq`).
  if β == nat then
    let vals : List Nat ← match m with
      | none => unsafe evalExpr (List Nat) (mkApp (mkConst ``List [0]) nat) (valsOf (mkConst f))
      | some _ => do
        let rows ← unsafe evalExpr (List (List Nat)) listTy (valsOf (mkConst f))
        pure rows.flatten
    let w := max 1 (vals.foldl (fun w v => max w v.log2.succ) 0)
    let N := vals.foldr (fun v acc => v ||| (acc <<< w)) 0
    let lemma (g : Expr) : Expr := match m with
      | none => mkApp5 (mkConst ``Lit.packed_eq) g (mkNatLit n.getNat) (mkNatLit w) (mkNatLit (2 ^ w))
          (mkNatLit N)
      | some m => mkApp6 (mkConst ``Lit.packed2_eq) g (mkNatLit n.getNat) (mkNatLit m.getNat) (mkNatLit w)
          (mkNatLit (2 ^ w)) (mkNatLit N)
    -- The hypothesis of the lemma, for `g`: its values are the table's.
    let hTyOf (g : Expr) : MetaM Expr := do return (← whnfR (← inferType (lemma g))).bindingDomain!
    let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    -- By evaluation, of `f` with the literals it reaches (`unfoldToLits`) if any.
    let h ← match ← unfoldToLits f (mkConst f) with
      | none => pure refl
      | some (f', prfF) =>
        let motive ← withLocalDeclD `g fty fun g => do mkLambdaFVars #[g] (← hTyOf g)
        pure <| mkApp4 (mkConst ``Eq.mpr [0]) (← hTyOf (mkConst f)) (← hTyOf f')
          (mkApp6 (mkConst ``congrArg [1, 1]) fty (mkSort 0) (mkConst f) f' motive prfF) refl
    let prf := mkApp (lemma (mkConst f)) h
    let some (_, _, litV) := (← inferType prf).eq?
      | throwError "materialize_table: unexpected {← inferType prf}"
    addDecl (forceExpose := true) <| .defnDecl {
      name := f ++ `lit, levelParams := [], type := fty, value := litV
      hints := .abbrev, safety := .safe }
    addDecl <| .thmDecl {
      name := f ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) fty (mkConst f) (mkConst (f ++ `lit))
      value := prf }
    return
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) listTy)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) listTy inst
    (valsOf (mkConst f)))
  let l := ShareCommon.shareCommon' l
  -- `valsOf f = l`: by evaluation, of `f` with the literals it reaches
  -- (`unfoldToLits`) if any, so that a table built from tables reads them.
  let refl := mkApp2 (mkConst ``Eq.refl [1]) listTy l
  let hvals ← match ← unfoldToLits f (mkConst f) with
    | none => pure refl
    | some (f', prfF) =>
      let motive ← withLocalDeclD `g fty fun g => mkLambdaFVars #[g] (valsOf g)
      pure <| mkApp6 (mkConst ``Eq.trans [1]) listTy (valsOf (mkConst f)) (valsOf f') l
        (mkApp6 (mkConst ``congrArg [1, 1]) fty listTy (mkConst f) f' motive prfF) refl
  let litV ← match m with
    | none => withLocalDeclD `i nat fun i =>
        mkLambdaFVars #[i] (lookup l i i (mkApp (mkConst f) i))
    | some _ => withLocalDeclD `i nat fun i => withLocalDeclD `j nat fun j =>
        mkLambdaFVars #[i, j] (lookup l i j (mkApp2 (mkConst f) i j))
  let prf := match m with
    | none => mkApp5 (mkConst ``Lit.table_eq) β (mkConst f) (mkNatLit n.getNat) l hvals
    | some m => mkApp6 (mkConst ``Lit.table2_eq) β (mkConst f) (mkNatLit n.getNat) (mkNatLit m.getNat) l hvals
  addDecl (forceExpose := true) <| .defnDecl {
    name := f ++ `lit, levelParams := [], type := fty, value := litV
    hints := .abbrev, safety := .safe }
  addDecl <| .thmDecl {
    name := f ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) fty (mkConst f) (mkConst (f ++ `lit))
    value := ShareCommon.shareCommon' prf }

namespace Lit

/-- Defines `N.lit`, the value of the closed term `v` (of a type with a
`ToExpr` instance) as a literal, and `N.lit_eq : v = N.lit`, by evaluation
(reading the literals `v` reaches). -/
meta def materializeValue (N : Name) (v : Expr) : MetaM Unit := do
  let ty ← instantiateMVars (← inferType v)
  if ty.hasLevelParam || ty.hasMVar then throwError "materialize_value: {v} is universe polymorphic"
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst v)
  addDecl (forceExpose := true) <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
    hints := .abbrev, safety := .safe }
  -- By evaluation, of `v` with the literals it reaches (`unfoldToLits`) if any.
  let prf ← litProof N ty v
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) ty v (mkConst (N ++ `lit))
    value := ShareCommon.shareCommon' prf }

end Lit

open Lit in
/-- `materialize_value c`, for a closed constant `c` whose type has a `ToExpr`
instance (e.g. a list of instructions that several programs contain),
defines `c.lit`, its value as a literal, and `c.lit_eq : c = c.lit`, which the
kernel checks once, by evaluation; `materialize_value N := t` does the same for
the closed term `t`, as `N.lit` and `N.lit_eq`. The literals of code that
contains it then read it (`materialize_code`), as for `materialize_table`. -/
syntax "materialize_value " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_value $id:ident) => liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    unless (← getConstInfo c).levelParams.isEmpty do
      throwError "materialize_value: {c} is universe polymorphic"
    materializeValue c (mkConst c)
  | `(materialize_value $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_value: {e} is not closed"
    materializeValue ((← getCurrNamespace) ++ id.getId) e

open Lit in
/-- `materialize_code foo` defines `foo.lit`, the value of the code `foo` as a
literal (calling the literals of the code materialized before), and
`foo.lit_eq : foo = foo.lit`; `materialize_code N := t` does the same for the
closed code term `t`, as `N.lit` and `N.lit_eq`. -/
syntax "materialize_code " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_code $id:ident) => liftTermElabM do
    let foo ← realizeGlobalConstNoOverloadWithInfo id
    materialize foo (mkConst foo)
  | `(materialize_code $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_code: {e} is not closed"
    materialize ((← getCurrNamespace) ++ id.getId) e

open Lit in
/-- `materialize_template N := f x₁ … xₖ`, for code that is a function of
offsets (`Nat → … → Nat → α`): `N.lit`, that function as a literal with the
offsets free, and `N.lit_eq : f x₁ … xₖ = N.lit`, which the literals of code
calling `f x₁ … xₖ` then read rather than evaluating `f` at each call (see
"Templates" in `Lit.lean`). -/
syntax "materialize_template " ident " := " term : command

open Lit in
elab_rules : command
  | `(materialize_template $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    materializeTemplate ((← getCurrNamespace) ++ id.getId) e

namespace Lit

/-- The value `v` of a constant with a literal, and the code it unfolds to, a
few definitions deep (each with its head unfolded, while that is a definition
of this project's code): a goal can name any of them for the constant, as a
generic proof's `exchangeWith c mq` for `exchangeP256 := Cfg.exchangeJA p256 …`,
which unfolds to it. -/
meta def unfoldChain (env : Environment) (mods : Array Name) (v : Expr) (depth : Nat := 4) :
    Array Expr := Id.run do
  let ok (e : Expr) := e.isApp && e.getAppFn.isConst && !e.hasLooseBVars
  unless ok v do return #[]
  let mut out := #[v]
  let mut cur := v
  for _ in [0:depth] do
    let .const g ls := cur.getAppFn | break
    unless codeModule env mods g do break
    let some (.defnInfo d) := env.find? g | break
    let next := ((d.value.instantiateLevelParams d.levelParams ls).betaRev cur.getAppRevArgs).headBeta
    unless ok next do break
    out := out.push next
    cur := next
  return out

/-- The closed subterms of `tgt` that are `v` up to its arguments: the same
head and number of arguments, each argument the same, or (an argument that is
not code, whose comparison could build it) definitionally equal by the
kernel's check (a configuration written another way). -/
meta def unfoldedOccurrences (tgt v : Expr) : MetaM (Array Expr) := do
  let f := v.getAppFn
  let n := v.getAppNumArgs
  let found ← IO.mkRef (#[] : Array Expr)
  tgt.forEach fun t => do
    if t.getAppFn == f && t.getAppNumArgs == n && !t.hasLooseBVars && !t.hasMVar then
      found.modify fun a => if a.contains t then a else a.push t
  let env ← getEnv
  let mut out := #[]
  for t in ← found.get do
    let mut same := true
    for i in [0:n] do
      let a := t.getArg! i
      let b := v.getArg! i
      if a == b then continue
      let ty ← whnfR (← inferType a)
      if ty.isAppOf ``Code || ty.isAppOf ``List || a.hasFVar ||
          !Kernel.isDefEqGuarded env {} a b then
        same := false
        break
    if same then out := out.push t
  return out

/-- With `VG_RW_LIT_REPORT` set to a file, a line there for each code that
`rw_lit` found unfolded (`unfoldChain`) rather than named: where a proof
names the code by its generator. -/
meta def reportUnfolded (N : Name) (v : Expr) : MetaM Unit := do
  let some path ← IO.getEnv "VG_RW_LIT_REPORT" | return
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn s!"{← getMainModule} {N} {v.getAppFn.constName!}"

end Lit

open Elab Tactic Lit in
/-- Rewrites each code of the goal that has a literal (`materialize_code`) to it. -/
elab "rw_lit" : tactic => withMainContext do
  -- Only code whose head constant the goal mentions can occur in it.
  let used := (← instantiateMVars (← getMainTarget)).getUsedConstantsAsSet
  let env ← getEnv
  let mods := env.header.moduleNames
  -- (`litNames` scans every constant of the project's modules: once a call.)
  let names := litNames env
  for N in names do
    let lhs ← lhsOf N
    -- A constant's code as the goal may have it unfolded: a generic proof's
    -- `Cfg.verify p384` for `verifyP384 := Cfg.verify p384`. Rewritten as a whole
    -- (`N.lit_eq` at `value = N.lit`, which the kernel checks by delta), rather than
    -- unfolded below, where the kernel would build the code again from the
    -- functions it is made of (e.g. 30 s rather than 2 s for P-384's verification).
    if let .const c [] := lhs then
      if let some (.defnInfo d) := env.find? c then
        if d.levelParams.isEmpty then
          for v in unfoldChain env mods d.value do
            unless used.contains v.getAppFn.constName! do continue
            let tgt ← instantiateMVars (← getMainTarget)
            for t in ← unfoldedOccurrences tgt v do
              let tgt ← instantiateMVars (← getMainTarget)
              let ty ← inferType lhs
              let u ← getLevel ty
              -- `N.lit_eq` at `t = N.lit`, which the kernel checks by delta.
              let prf ← mkExpectedTypeHint (mkConst (N ++ `lit_eq))
                (mkApp3 (mkConst ``Eq [u]) ty t (mkConst (N ++ `lit)))
              let motive ← withLocalDeclD `y ty fun y =>
                mkLambdaFVars #[y] (tgt.replace fun x => if x == t then some y else none)
              let g ← getMainGoal
              let tgt' := tgt.replace fun x => if x == t then some (mkConst (N ++ `lit)) else none
              replaceMainGoal [← g.replaceTargetEq tgt'
                (mkApp6 (mkConst ``congrArg [u, 1]) ty (mkSort 0) t (mkConst (N ++ `lit)) motive prf)]
              reportUnfolded N v
    unless lhs.getAppFn.isConst && used.contains lhs.getAppFn.constName! do continue
    let tgt ← instantiateMVars (← getMainTarget)
    if (tgt.find? (· == lhs)).isNone then continue
    let g ← getMainGoal
    let r ← g.rewrite tgt (mkConst (N ++ `lit_eq))
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)
  -- The definitions of the goal that lead to constants with a literal
  -- (`materialize_table`, code used other than as a call), unfolded, and
  -- those constants rewritten to their literals.
  -- Each is rewritten on its own, and then in the goal with one `congrArg`:
  -- the goal can be large (a hint of `taint_decide`), and the kernel
  -- instantiates the motive of each rewrite of it.
  let tgt ← instantiateMVars (← getMainTarget)
  for s in ← reachingSubterms names tgt do
    let some (s', prf) ← unfoldToLits .anonymous s (some names) | continue
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let ty ← inferType s
    let motive ← withLocalDeclD `y ty fun y =>
      mkLambdaFVars #[y] (tgt.replace fun t => if t == s then some y else none)
    let eqPrf := mkApp6 (mkConst ``congrArg [← getLevel ty, 1]) ty (mkSort 0) s s' motive prf
    replaceMainGoal [← g.replaceTargetEq (tgt.replace fun t => if t == s then some s' else none) eqPrf]

/-- `decide +kernel`, after rewriting the code constants of the goal to their
literals (`rw_lit`). -/
macro "lit_decide" : tactic => `(tactic| (rw_lit; decide +kernel))

end VG
