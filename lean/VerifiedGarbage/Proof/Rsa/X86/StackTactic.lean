module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public meta import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import Lean.Elab.Tactic

/-! # Compositional stack checks for RSA callers of the large square schedules

Each structured node is proved from its children, and a code that occurs
again by the proof of its first occurrence. The Montgomery callee and the
given theorems (`rsa_stack_shape [h, …]`, for any arguments of their code)
are reused; only straight-line blocks are evaluated.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.StackShape
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare

 theorem loop_all {b : Prog isa} (c : Cond) (h : b.allInstrs noSp=true) :
    (Code.loop b c).allInstrs noSp=true := h
 theorem call_all {b : Prog isa} (name : String) (h : b.allInstrs noSp=true) :
    (Code.call name b).allInstrs noSp=true := h
 theorem frame_all {b : Prog isa} {i j : Instr} (hi : noSp i=true) (h : b.allInstrs noSp=true) (hj : noSp j=true) :
    (Code.frame i b j).allInstrs noSp=true := by change noSp i && b.allInstrs noSp && noSp j=true; rw [hi,h,hj]; rfl

 theorem block_stack (is : List Instr) : stackUse (.block is : Prog isa)=0 := rfl
 theorem seq_stack (a b : Prog isa) (m n : Nat) (ha : stackUse a=m) (hb : stackUse b=n) :
    stackUse (.seq a b)=max m n := by rw [stackUse,ha,hb]
 theorem ite_stack (c : Cond) (a b : Prog isa) (m n : Nat) (ha : stackUse a=m) (hb : stackUse b=n) :
    stackUse (.ite c a b)=max m n := by rw [stackUse,ha,hb]
 theorem loop_stack (c : Cond) (a : Prog isa) (n : Nat) (ha : stackUse a=n) :
    stackUse (.loop a c)=n := ha
 theorem call_stack (name : String) (a : Prog isa) (n : Nat) (ha : stackUse a=n) :
    stackUse (.call name a)=n+4 := by rw [stackUse,ha]
 theorem frame_stack (i j : Instr) (a : Prog isa) (n : Nat) (ha : stackUse a=n) :
    stackUse (.frame i a j)=n+frameBytes i := by rw [stackUse,ha]

end VG.Proof.Rsa.X86.StackShape

public meta section
namespace VG.Proof.Rsa.X86.StackShape
open Lean Meta Elab Tactic

mutual

/-- Proves `code.allInstrs noSp = true` from its children. A code that occurs
again (callees' loops, selection blocks) takes the goal proved first:
`memo` maps each closed code proved so far to its goal. -/
partial def proveNode (g : MVarId) (leaves : Array Expr) (memo : IO.Ref (Std.HashMap Expr MVarId)) :
    TacticM Unit := do
  setGoals [g]
  let ty ← instantiateMVars (← g.getType)
  let some (_,lhs,_) := ty.eq? | throwError "rsa_stack_shape: expected a Boolean equality"
  if !lhs.isAppOfArity ``VG.Code.allInstrs 4 then
    evalTactic (← `(tactic| lit_decide))
    return
  let code := lhs.getAppArgs.back!
  let closed := !code.hasFVar && !code.hasMVar
  if closed then
    if let some g' := (← memo.get)[code]? then
      g.assign (mkMVar g')
      setGoals []
      return
  proveNode' g code leaves memo
  if closed then memo.modify (·.insert code g)

/-- `proveNode` for a code not proved before. -/
partial def proveNode' (g : MVarId) (code : Expr) (leaves : Array Expr)
    (memo : IO.Ref (Std.HashMap Expr MVarId)) : TacticM Unit := do
  if code.isConstOf ``VG.Impl.Mont.X86.Sse2.atBody then
    evalTactic (← `(tactic| exact VG.Proof.Mont.X86.Sse2.atBody_allNoSp))
    return
  -- A given theorem about code with the same head, for any of its arguments.
  if code.getAppFn.isConst then
    for leaf in leaves do
      let (mvs,_,leafTy) ← forallMetaTelescopeReducing (← inferType leaf)
      if let some (_,leafLhs,_) := leafTy.eq? then
        let leafCode := leafLhs.getAppArgs.back!
        if leafCode.getAppFn == code.getAppFn && leafCode.getAppArgs.size == code.getAppArgs.size then
          let mut matching := true
          for (a,b) in leafCode.getAppArgs.zip code.getAppArgs do
            unless ← isDefEq a b do matching := false
          if matching then
            g.assign (← instantiateMVars (mkAppN leaf mvs))
            setGoals []
            return
  let node ← whnf code
  match node.getAppFn.constName? with
  | some ``VG.Code.seq => evalTactic (← `(tactic| apply VG.Proof.Mont.X86.StaticSquare.seq_noSp))
  | some ``VG.Code.ite => evalTactic (← `(tactic| apply VG.Proof.Mont.X86.StaticSquare.ite_noSp))
  | some ``VG.Code.loop => evalTactic (← `(tactic| apply loop_all))
  | some ``VG.Code.call => evalTactic (← `(tactic| apply call_all))
  | some ``VG.Code.frame => evalTactic (← `(tactic| apply frame_all))
  | some ``VG.Code.block =>
    -- No code these callers check has a literal: `lit_decide`'s search
    -- for one would cost more than the kernel's check of the block.
    evalTactic (← `(tactic| decide +kernel))
    return
  | _ => throwError "rsa_stack_shape: unexpected code node {node}"
  let children ← getGoals
  for child in children do proveNode child leaves memo

end

partial def stackProof (code : Expr) : MetaM (Nat × Expr) := do
  if code.isConstOf ``VG.Impl.Mont.X86.Sse2.atBody then
    return (56,mkConst ``VG.Proof.Mont.X86.Sse2.atBody_stack)
  let node ← whnf code
  let args := node.getAppArgs
  match node.getAppFn.constName? with
  | some ``VG.Code.block =>
    return (0,← mkAppM ``block_stack #[args.back!])
  | some ``VG.Code.seq =>
    let a := args[args.size-2]!
    let b := args.back!
    let (m,ha) ← stackProof a
    let (n,hb) ← stackProof b
    return (max m n,← mkAppM ``seq_stack #[a,b,mkNatLit m,mkNatLit n,ha,hb])
  | some ``VG.Code.ite =>
    let c := args[args.size-3]!
    let a := args[args.size-2]!
    let b := args.back!
    let (m,ha) ← stackProof a
    let (n,hb) ← stackProof b
    return (max m n,← mkAppM ``ite_stack #[c,a,b,mkNatLit m,mkNatLit n,ha,hb])
  | some ``VG.Code.loop =>
    let a := args[args.size-2]!
    let c := args.back!
    let (n,ha) ← stackProof a
    return (n,← mkAppM ``loop_stack #[c,a,mkNatLit n,ha])
  | some ``VG.Code.call =>
    let name := args[args.size-2]!
    let a := args.back!
    let (n,ha) ← stackProof a
    return (n+4,← mkAppM ``call_stack #[name,a,mkNatLit n,ha])
  | some ``VG.Code.frame =>
    let i := args[args.size-3]!
    let a := args[args.size-2]!
    let j := args.back!
    let (n,ha) ← stackProof a
    let bytes ← whnf (mkApp (mkConst ``VG.X86.frameBytes) i)
    let some extra := bytes.nat? <|> bytes.rawNatLit? | throwError "rsa_stack_use: nonliteral frame size {bytes}"
    return (n+extra,← mkAppM ``frame_stack #[i,j,a,mkNatLit n,ha])
  | _ => throwError "rsa_stack_use: unexpected code node {node}"

elab "rsa_stack_use" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_,lhs,_) := ty.eq? | throwError "rsa_stack_use: expected an equality"
  unless lhs.isAppOfArity ``VG.X86.stackUse 1 do throwError "rsa_stack_use: expected stackUse"
  let (_,proof) ← stackProof lhs.getAppArgs.back!
  goal.assign proof
  replaceMainGoal []

elab "rsa_stack_shape" : tactic => do
  let goals ← getGoals
  let some main := goals.head? | throwNoGoalsToBeSolved
  proveNode main #[] (← IO.mkRef {})
  setGoals goals.tail!

elab "rsa_stack_shape" "[" hs:term,* "]" : tactic => do
  let goals ← getGoals
  let some main := goals.head? | throwNoGoalsToBeSolved
  let leaves ← hs.getElems.mapM fun h => Elab.Term.elabTerm h none
  proveNode main leaves (← IO.mkRef {})
  setGoals goals.tail!

end VG.Proof.Rsa.X86.StackShape
