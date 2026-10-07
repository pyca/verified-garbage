import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Certificate

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

/-- Certificate construction is untrusted; its result is checked by `certDom`. -/
def intern (nodes : Array Node) (key : Node) : Array Node × Nat :=
  match (List.range nodes.size).find? (fun i => decide (nodes[i]?=some key)) with
  | some n => (nodes,n)
  | none => (nodes.push key,nodes.size)

def buildStep (size : Nat) (nodes : Array Node) (e : Env Nat) (i : Instr) : Option (Array Node × Env Nat) := do
  let view ← decode i
  match view.val with
  | .scalar op d a b c =>
    if d=.x0 || !op.valid then none else do
      let va ← arg {zero:=0,applyOp:=fun _ _ _ _ _ _ => none} e op.useA a
      let vb ← arg {zero:=0,applyOp:=fun _ _ _ _ _ _ => none} e op.useB b
      let vc ← arg {zero:=0,applyOp:=fun _ _ _ _ _ _ => none} e op.useC c
      let vd ← arg {zero:=0,applyOp:=fun _ _ _ _ _ _ => none} e op.useD d
      let cf ← if op.useCarry then e.carry else some 0
      let (ns,vr) := if op=.logic .orr ∧ va=vb then (nodes,va)
        else intern nodes (.app op va vb vc vd cf)
      return (ns,{e.setReg d vr with carry:=if op.flags then some vr else e.carry})
  | .load d off =>
    if d=.x0 || !(off%8=0 && off+8≤size && off<32768) then none
    else some (nodes,e.setReg d (e.slot off))
  | .store r off =>
    if !(off%8=0 && off+8≤size && off<32768) then none
    else (e.reg r).map (fun a => (nodes,e.setSlot off a))

def build (size : Nat) : List Instr → Array Node → Env Nat → Option (Array Node × Env Nat)
  | [],nodes,e => some (nodes,e)
  | i::is,nodes,e => do
    let (ns,en) ← buildStep size nodes e i
    build size is ns en

def initialNodes (size : Nat) : Array Node :=
  #[.zero] ++ ((List.range (size/8)).map (fun i => Node.input (8*i))).toArray

def initialEnv : Env Nat := {reg:=fun _ => none,slot:=fun off => off/8+1,carry:=none}

def balanced {α : Type} : Nat → List (Nat × α) → Tree α
  | 0,_ => .empty
  | n+1,xs =>
    let m := xs.length/2
    match xs[m]? with
    | none => .empty
    | some (k,v) => .node k v (balanced n (xs.take m)) (balanced n (xs.drop (m+1)))

def toCertificate (nodes : Array Node) : Certificate :=
  let xs := nodes.toList.zipIdx.map (fun (v,k) => (k,v))
  let hints := (xs.map (fun (k,v) => (v.key,k))).mergeSort (fun a b => a.1≤b.1)
  ⟨balanced xs.length xs,balanced hints.length hints⟩

def buildPair (size : Nat) (original optimized : List Instr) : Option Certificate := do
  let (ns,_) ← build size original (initialNodes size) initialEnv
  let (ns,_) ← build size optimized ns initialEnv
  return toCertificate ns

end VG.Proof.Weierstrass.AArch64.Forward
