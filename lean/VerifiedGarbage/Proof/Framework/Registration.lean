module

public import VerifiedGarbage.TCB.Registration
public meta import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.SpTest
public meta import VerifiedGarbage.Proof.Framework.SpTest
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The default proofs of a registration

Untrusted: this only changes how proofs are found; the kernel checks them.

The tactics `TCB/Registration.lean` declares for the default proofs of a
`Registration`, which a registration file imports this module for:

* `of_sig` proves `ofSig`, `∃ pre post leak, contract = sig.contract A pre
  post writeArgs stack leak`, by unfolding the head of `contract` until it is
  `Sig.contract` (e.g. `nttInvContract A` to `inPlaceContract A nttInv` to
  `Sig.contract A (inPlaceSig "f") …`), and then `⟨_, _, _, rfl⟩`, whose
  unification does not always find the arguments of `Sig.contract` itself.
* `consts_of` gives `consts`, the tables of constants in the contract
  `verified` proves (the goal `ConstsOf contract`): the tables `cs` of the
  first `Abi.withConsts A cs` in it, where it states them (the contract on
  `A.withConsts cs` of a proof that names the tables, e.g.
  `expandKeyContract (AArch64.abi.withConsts initConsts)`), else in the
  calling convention of the `Sig.contract` it unfolds to (as `of_sig`
  unfolds it), whose head is unfolded until it is an application of
  `Abi.withConsts`; and none if there is no such application.
* `stack_of` gives `stack`, the stack that the contract `verified` proves
  is for (the goal `StackOf contract`): the `stack` of the `Sig.contract` it
  unfolds to (as `of_sig` unfolds it), as that contract states it, so that
  `ofApi` and `ofSig` compare a number with itself; and 0 if it does not
  unfold to one, which `ofSig` then reports.
* `sp_safe` proves `spSafe`, `code.all (fun i => !T.isa.writesSp i) = true`:
  on the ISAs whose `writesSp` is always `false` (ARMv7, AArch64, PPC64LE) by
  `Code.all_of_forall`, which evaluates nothing, and on the others (x86,
  x86-64) by `Code.all_of_spTest (by lit_decide)`, which evaluates the ISA's
  cheaper test (`SpTest`, `Proof/Framework/SpTest.lean`) on the code's
  literal if the module imports the one that materializes it (`Lit.lean`),
  or, where that exceeds the recursion limit (rewriting some code to its
  literal), by `decide +kernel`; and with `M.writesSp` itself
  (`Code.all_of_allInstrs`) in a module that does not import the ISA's test.
  Code that depends on a variable of an enumeration (`adx : Bool`, a
  variant's `FieldVariant`) is proven for each of its values, by cases.
-/

@[expose] public section

namespace VG

/-- What a form that builds a scrubbed registration takes: code with its
proof of `Verified`, and what else a `Registration` states, with the same
fields and defaults, so that a call site writes it as it would a
registration (`{ code := c, verified := h }`). It is not a registration: the
form's result is, with the proof that the code it built returns without
secret residue (`VerifiedScrubbed`). -/
structure Unscrubbed (api : Api) (target : Target) where
  /-- `Registration.suffix`. -/
  suffix : String := ""
  /-- `Registration.tables`. -/
  tables : List (String × List FnTable) := []
  code : Prog target.isa
  /-- `Registration.contract`. -/
  contract : Contract target.isa :=
    api.contract (target.abi.withTables api.sig tables) 0
  verified : Verified target code contract
  /-- `Registration.consts`. -/
  consts : ConstsOf contract := by consts_of
  /-- `Registration.stack`. -/
  stack : StackOf contract := by stack_of
  ofApi : contract = api.contract ((target.abi.withConsts consts).withTables api.sig tables) stack := by
    exact rfl
  /-- `Registration.ofSig`. -/
  ofSig : ∃ pre post leak,
      contract = api.sig.contract
        ((target.abi.withConsts consts).withTables api.sig tables) pre post
        api.writeArgs stack leak := by
    of_sig
  /-- `Registration.spSafe`. -/
  spSafe : code.all (fun i => !target.isa.writesSp i) = true := by sp_safe
  /-- `Registration.written`. -/
  written : List (String × Nat) := []
  /-- `Registration.writtenOk`. -/
  writtenOk : ∀ s t s', contract.pre s → Exec target.isa code s t s' →
      Sig.writtenWithin target.abi api.sig written s s' := by
    exact fun _ _ _ _ _ => True.intro
  /-- `Registration.extra`. -/
  extra : List String := []
  /-- `Registration.vendor`. -/
  vendor : Option String := none
  /-- `Registration.notWith`. -/
  notWith : List String := []

/-- `Abi.withConsts` leaves the pointer width as it is. -/
theorem Abi.ptrBits_withConsts {M : ISA} (A : Abi M) (cs : List (String × List (BitVec 64))) :
    (A.withConsts cs).ptrBits = A.ptrBits := by
  unfold Abi.withConsts
  split <;> rfl

/-- `Abi.withTables` leaves the pointer width as it is. -/
theorem Abi.ptrBits_withTables {M : ISA} (A : Abi M) (sig : Sig) (ts : List (String × List FnTable)) :
    (A.withTables sig ts).ptrBits = A.ptrBits := by
  unfold Abi.withTables
  split <;> rfl

/-- A result's bits under a calling convention with tables of constants and
of functions are its bits under the calling convention: what
`Registration.verified` states them with. -/
theorem Abi.retBits_withConsts_withTables {M : ISA} (A : Abi M) (sig sig' : Sig)
    (cs : List (String × List (BitVec 64))) (ts : List (String × List FnTable)) :
    sig.retBits ((A.withConsts cs).withTables sig' ts).ptrBits = sig.retBits A.ptrBits := by
  rw [Abi.ptrBits_withTables, Abi.ptrBits_withConsts]

/-- `VerifiedScrubbed` proven for the result's bits under the calling
convention with its tables is `VerifiedScrubbed` as a registration states it
(`Abi.retBits_withConsts_withTables`). -/
theorem VerifiedScrubbed.abi {T : Target} {c : Prog T.isa} {k : Contract T.isa} {sig sig' : Sig}
    {cs : List (String × List (BitVec 64))} {ts : List (String × List FnTable)}
    (h : VerifiedScrubbed T c k (sig.retBits ((T.abi.withConsts cs).withTables sig' ts).ptrBits)) :
    VerifiedScrubbed T c k (sig.retBits T.abi.ptrBits) :=
  Abi.retBits_withConsts_withTables T.abi sig sig' cs ts ▸ h

end VG

end

public meta section

namespace VG.RegistrationTactics

open Lean Meta Elab Tactic

/-- The left-hand side of the equation under the existential quantifiers
of `e`. -/
partial def eqLhs : Expr → Option Expr
  | .app (.app (.const ``Exists _) _) (.lam _ _ b _) => eqLhs b
  | e => e.eq?.map (·.2.1)

/-- `e` with its head unfolded until it is an application of `Sig.contract`. -/
partial def toSigContract (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  if e.isAppOf ``Sig.contract then return e
  match ← unfoldDefinition? e with
  | some e' => toSigContract e'
  | none => throwError "of_sig: {e} does not unfold to an application of `Sig.contract`"

elab_rules : tactic
  | `(tactic| of_sig) => do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let some c := eqLhs ty | throwError "of_sig: the goal is not `∃ pre post leak, _ = _`: {ty}"
    if c.hasLooseBVars then throwError "of_sig: the contract depends on `pre`, `post` or `leak`: {ty}"
    let c' ← toSigContract c
    setGoals [← g.replaceTargetDefEq (ty.replace fun e => if e == c then some c' else none)]
    evalTactic (← `(tactic| exact ⟨_, _, _, rfl⟩))

/-- The tables `cs` of the first application `Abi.withConsts A cs` in `e` that
has neither loose bound variables nor metavariables. -/
def findConsts? (e : Expr) : Option Expr :=
  (e.find? fun e => e.isAppOfArity ``Abi.withConsts 3 && !e.hasLooseBVars && !e.hasMVar).map
    (·.appArg!)

/-- The tables of constants of the calling convention `A`: those of the first
application of `Abi.withConsts` in it, with its head unfolded until there is
one, or none. -/
partial def abiConsts? (A : Expr) : MetaM (Option Expr) := do
  if let some cs := findConsts? A then return some cs
  match ← unfoldDefinition? A with
  | some A' => abiConsts? (← whnfCore A')
  | none => return none

elab_rules : tactic
  | `(tactic| consts_of) => do
    let g ← getMainGoal
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    unless ty.isAppOfArity ``ConstsOf 2 do
      throwError "consts_of: the goal is not `ConstsOf contract`: {ty}"
    let c := ty.appArg!
    if c.hasMVar then
      throwError "consts_of: the contract is not known; give `consts`: {c}"
    let cs? ← match findConsts? c with
      | some cs => pure (some cs)
      | none =>
        let s ← saveState
        try
          let c' ← toSigContract c
          -- `Sig.contract A sig pre post writeArgs stack leak`, implicit `M` first.
          abiConsts? (c'.getArg! 1)
        catch _ =>
          s.restore
          pure none
    match cs? with
    | some cs =>
      unless ← isDefEq (← inferType cs) (← g.getType) do
        throwError "consts_of: {cs} is not a list of tables of constants"
      g.assign cs
    | none => evalTactic (← `(tactic| exact []))

elab_rules : tactic
  | `(tactic| stack_of) => do
    let g ← getMainGoal
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    unless ty.isAppOfArity ``StackOf 2 do
      throwError "stack_of: the goal is not `StackOf contract`: {ty}"
    let c := ty.appArg!
    if c.hasMVar then
      throwError "stack_of: the contract is not known; give `contract`: {c}"
    let s ← saveState
    let n? ← try
        let c' ← toSigContract c
        -- `Sig.contract A sig pre post writeArgs stack leak`, implicit `M` first.
        pure (if c'.getAppNumArgs ≥ 7 then some (c'.getArg! 6) else none)
      catch _ =>
        s.restore
        pure none
    match n? with
    | some n =>
      if n.hasMVar then
        throwError "stack_of: the contract's stack is not known; give `stack`: {n}"
      unless ← isDefEq (← inferType n) (← g.getType) do
        throwError "stack_of: {n} is not a number of bytes"
      g.assign n
    | none => evalTactic (← `(tactic| exact (0 : Nat)))

/-- A free variable of `e` whose type is an enumeration (`Bool`, an
`inductive` of constructors without fields). -/
def enumFVar? (e : Expr) : MetaM (Option FVarId) := do
  for fv in (collectFVars {} e).fvarIds do
    let ty ← whnf (← fv.getType)
    let .const n _ := ty | continue
    let some (.inductInfo i) := (← getEnv).find? n | continue
    if i.isRec || i.numIndices > 0 then continue
    if ← i.ctors.allM fun c => return (← getConstInfoCtor c).numFields == 0 then
      return some fv
  return none

elab_rules : tactic
  | `(tactic| sp_safe) => do
    let ty ← instantiateMVars (← getMainTarget)
    let some (_, lhs, _) := ty.eq? | throwError "sp_safe: the goal is not `Code.all p c = true`: {ty}"
    unless lhs.isAppOfArity ``Code.all 4 do
      throwError "sp_safe: the goal is not `Code.all p c = true`: {ty}"
    let p := lhs.getArg! 2
    -- Whether `p` holds of every instruction by evaluation alone.
    let always ← withLocalDeclD `i (lhs.getArg! 0) fun i => do
      return (← whnf (mkApp p i)).isConstOf ``Bool.true
    if always then
      evalTactic (← `(tactic| exact Code.all_of_forall (fun _ => rfl) _))
    else if let some fv ← enumFVar? lhs then
      let gs ← (← getMainGoal).cases fv
      for g in gs do
        setGoals [g.mvarId]
        evalTactic (← `(tactic| sp_safe))
    else
      let s ← saveState
      -- The recursion limit is a runtime exception, which `first` does not catch.
      -- The ISA's cheaper test (`SpTest`), where its proofs give one and the module imports it.
      tryCatchRuntimeEx (evalTactic (← `(tactic| first
          | exact Code.all_of_spTest (by lit_decide)
          | exact Code.all_of_allInstrs (by lit_decide))))
        fun _ => do
          s.restore
          evalTactic (← `(tactic| first
            | exact Code.all_of_spTest (by decide +kernel)
            | exact Code.all_of_allInstrs (by decide +kernel)))

end VG.RegistrationTactics
