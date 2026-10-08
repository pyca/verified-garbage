import VerifiedGarbage.TCB.AArch64.Target

/-! Executable certificate and environment data. The original proof modules
validate every generated certificate and execution using the kernel. -/
namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

inductive Op where
  | add | sub | adds | adcs | subs | sbcs | adc | sbc | csel
  | logic (o : LogicOp)
  | mul | umulh | madd
  | lsl (n : Nat) | lsr (n : Nat) | extr (n : Nat)
  | movz (v : BitVec 16) (n : Nat) | movk (v : BitVec 16) (n : Nat)
  deriving DecidableEq, Repr

def Op.instr : Op → Reg → Reg → Reg → Reg → Instr
  | .add,d,a,b,_ => .add .x d a b
  | .sub,d,a,b,_ => .sub .x d a b
  | .adds,d,a,b,_ => .adds .x d a b
  | .adcs,d,a,b,_ => .adcs .x d a b
  | .subs,d,a,b,_ => .subs .x d a b
  | .sbcs,d,a,b,_ => .sbcs .x d a b
  | .adc,d,a,b,_ => .adc .x d a b
  | .sbc,d,a,b,_ => .sbc .x d a b
  | .csel,d,a,b,_ => .csel .x d a b
  | .logic o,d,a,b,_ => .logic o .x d a b
  | .mul,d,a,b,_ => .mul .x d a b
  | .umulh,d,a,b,_ => .umulh d a b
  | .madd,d,a,b,c => .madd .x d a b c
  | .lsl n,d,a,_,_ => .lsl .x d a n
  | .lsr n,d,a,_,_ => .lsr .x d a n
  | .extr n,d,a,b,_ => .extr .x d a b n
  | .movz v n,d,_,_,_ => .movz .x d v n
  | .movk v n,d,_,_,_ => .movk .x d v n

def Op.valid : Op → Bool
  | .lsl n | .lsr n | .extr n => n<64
  | .movz _ n | .movk _ n => 16*n<64
  | _ => true

def Op.flags : Op → Bool
  | .adds | .adcs | .subs | .sbcs => true
  | _ => false

/-- Canonical registers hold the operands, including the old destination for MOVK. -/
def scalarState (a b c d : BitVec 64) (carry : Bool) : State :=
  { gpr := fun r => if r=.x1 then a else if r=.x2 then b else if r=.x3 then c
      else if r=.x8 then d else 0
    sp:=0,c:=carry,mem:=fun _ => 0,rd:=[],wr:=[] }

def Op.useA : Op → Bool
  | .movz .. | .movk .. => false
  | _ => true

def Op.useB : Op → Bool
  | .lsl .. | .lsr .. | .movz .. | .movk .. => false
  | _ => true

def Op.useC : Op → Bool
  | .madd => true
  | _ => false

def Op.useD : Op → Bool
  | .movk .. => true
  | _ => false

def Op.useCarry : Op → Bool
  | .adcs | .sbcs | .adc | .sbc | .csel => true
  | _ => false

def Op.eval (op : Op) (a b c d : BitVec 64) (carry : Bool) : BitVec 64 × Bool :=
  let s := scalarState (if op.useA then a else 0) (if op.useB then b else 0)
    (if op.useC then c else 0) (if op.useD then d else 0) (op.useCarry && carry)
  let t := (exec (op.instr .x8 .x1 .x2 .x3) s).getD s
  (t.gpr .x8,t.c)


inductive Decoded where
  | scalar (op : Op) (d a b c : Reg)
  | load (d : Reg) (off : Nat)
  | store (r : Reg) (off : Nat)

def Decoded.instr : Decoded → Instr
  | .scalar op d a b c => op.instr d a b c
  | .load d off => .ldr .x d .x0 off
  | .store r off => .str .x r .x0 off

/-- Only the scalar instruction forms actually used by field arithmetic are accepted. -/
def decode : (i : Instr) → Option {v : Decoded // v.instr=i}
  | .add .x d a b => some ⟨.scalar .add d a b .x0,rfl⟩
  | .sub .x d a b => some ⟨.scalar .sub d a b .x0,rfl⟩
  | .adds .x d a b => some ⟨.scalar .adds d a b .x0,rfl⟩
  | .adcs .x d a b => some ⟨.scalar .adcs d a b .x0,rfl⟩
  | .subs .x d a b => some ⟨.scalar .subs d a b .x0,rfl⟩
  | .sbcs .x d a b => some ⟨.scalar .sbcs d a b .x0,rfl⟩
  | .adc .x d a b => some ⟨.scalar .adc d a b .x0,rfl⟩
  | .sbc .x d a b => some ⟨.scalar .sbc d a b .x0,rfl⟩
  | .csel .x d a b => some ⟨.scalar .csel d a b .x0,rfl⟩
  | .logic o .x d a b => some ⟨.scalar (.logic o) d a b .x0,rfl⟩
  | .mul .x d a b => some ⟨.scalar .mul d a b .x0,rfl⟩
  | .umulh d a b => some ⟨.scalar .umulh d a b .x0,rfl⟩
  | .madd .x d a b c => some ⟨.scalar .madd d a b c,rfl⟩
  | .lsl .x d a n => some ⟨.scalar (.lsl n) d a .x0 .x0,rfl⟩
  | .lsr .x d a n => some ⟨.scalar (.lsr n) d a .x0 .x0,rfl⟩
  | .extr .x d a b n => some ⟨.scalar (.extr n) d a b .x0,rfl⟩
  | .movz .x d v n => some ⟨.scalar (.movz v n) d .x0 .x0 .x0,rfl⟩
  | .movk .x d v n => some ⟨.scalar (.movk v n) d .x0 .x0 .x0,rfl⟩
  | .ldr .x d .x0 off => some ⟨.load d off,rfl⟩
  | .str .x r .x0 off => some ⟨.store r off,rfl⟩
  | _ => none

structure Dom (α : Type) where
  zero : α
  applyOp : Op → α → α → α → α → α → Option α

structure Dom.Sound {α : Type} (D : Dom α) (v : α → BitVec 64 × Bool) : Prop where
  zero : (v D.zero).1=0 ∧ (v D.zero).2=false
  applyOp : ∀ op a b c d f r,D.applyOp op a b c d f=some r →
    (v r).1=(op.eval (v a).1 (v b).1 (v c).1 (v d).1 (v f).2).1 ∧
    (op.flags=true → (v r).2=(op.eval (v a).1 (v b).1 (v c).1 (v d).1 (v f).2).2)

structure Env (α : Type) where
  reg : Reg → Option α
  slot : Nat → α
  carry : Option α

variable {α : Type}

def Env.setReg (e : Env α) (d : Reg) (v : α) : Env α :=
  { e with reg:=fun r => if r=d then some v else e.reg r }

def Env.setSlot (e : Env α) (off : Nat) (v : α) : Env α :=
  { e with slot:=fun j => if j=off then v else e.slot j }

def arg (D : Dom α) (e : Env α) (use : Bool) (r : Reg) : Option α :=
  if use then e.reg r else some D.zero

def carryArg (D : Dom α) (e : Env α) (op : Op) : Option α :=
  if op.useCarry then e.carry else some D.zero

def decodedStep (D : Dom α) (size : Nat) (e : Env α) : Decoded → Option (Env α)
  | .scalar op d a b c => do
    if d=.x0 || !op.valid then none else do
      let va ← arg D e op.useA a
      let vb ← arg D e op.useB b
      let vc ← arg D e op.useC c
      let vd ← arg D e op.useD d
      let cf ← carryArg D e op
      let vr ← D.applyOp op va vb vc vd cf
      return {e.setReg d vr with carry:=if op.flags then some vr else e.carry}
  | .load d off => if d=.x0 || !(off%8=0 && off+8≤size && off<32768) then none
      else some (e.setReg d (e.slot off))
  | .store r off => if !(off%8=0 && off+8≤size && off<32768) then none
      else (e.reg r).map (e.setSlot off)

def step (D : Dom α) (size : Nat) (e : Env α) (i : Instr) : Option (Env α) := do
  let view ← decode i
  decodedStep D size e view.val

def eval (D : Dom α) (size : Nat) : List Instr → Env α → Option (Env α)
  | [],e => some e
  | i::is,e => (step D size e i).bind (eval D size is)

/-- The abstract state records only initialized field words and carry. -/
structure Rel (v : α → BitVec 64 × Bool) (base : Addr) (size : Nat) (e : Env α) (s : State) : Prop where
  reg : ∀ r a,e.reg r=some a → (v a).1=s.gpr r
  slot : ∀ off,off%8=0 → off+8≤size → (v (e.slot off)).1=s.mem.readW (base+BitVec.ofNat 64 off) 64
  carry : ∀ a,e.carry=some a → (v a).2=s.c


end VG.Proof.Weierstrass.AArch64.Forward
namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

inductive Tree (α : Type) where
  | empty : Tree α
  | node (key : Nat) (value : α) (left right : Tree α) : Tree α

namespace Tree

def lookup {α : Type} (key : Nat) : Tree α → Option α
  | .empty => none
  | .node k v left right =>
    bif Nat.beq key k then some v else bif Nat.blt key k then lookup key left else lookup key right

def all {α : Type} (P : Nat → α → Bool) : Tree α → Bool
  | .empty => true
  | .node k v left right => P k v && all P left && all P right


end Tree

/-- A shared acyclic expression table for the original and scheduled blocks. -/
inductive Node where
  | zero
  | input (off : Nat)
  | app (op : Op) (a b c d f : Nat)
  deriving DecidableEq, Repr

def Node.before (n : Node) (i : Nat) : Prop :=
  match n with
  | .app _ a b c d f => a<i ∧ b<i ∧ c<i ∧ d<i ∧ f<i
  | _ => True

instance (n : Node) (i : Nat) : Decidable (n.before i) := by
  cases n <;> unfold Node.before <;> infer_instance

/-- Lookup keys accelerate proof evaluation; every hint is checked against its node. -/
def Op.key : Op → Nat
  | .add => 0 | .sub => 1 | .adds => 2 | .adcs => 3 | .subs => 4 | .sbcs => 5
  | .adc => 6 | .sbc => 7 | .csel => 8
  | .logic .and => 9 | .logic .orr => 10 | .logic .eor => 11
  | .mul => 12 | .umulh => 13 | .madd => 14
  | .lsl n => 100+n | .lsr n => 200+n
  | .extr n => 300+n
  | .movz v n => 100000+64*v.toNat+n
  | .movk v n => 10000000+64*v.toNat+n

def Node.key : Node → Nat
  | .zero => 0
  | .input off => 1+3*off
  | .app op a b c d f => 2+3*(((((op.key*4096+a)*4096+b)*4096+c)*4096+d)*4096+f)

structure Certificate where
  nodes : Tree Node
  hints : Tree Nat

def CertValid (nodes : Certificate) : Prop :=
  nodes.nodes.lookup 0=some .zero ∧ nodes.nodes.all (fun i n => decide (n.before i))=true

instance (nodes : Certificate) : Decidable (CertValid nodes) := by
  unfold CertValid; infer_instance


/-- Boolean equality uses the kernel's native natural-number comparison. -/
def Node.eqB : Node → Node → Bool
  | .zero, .zero => true
  | .input a, .input b => Nat.beq a b
  | .app op a b c d f, .app op' a' b' c' d' f' =>
    decide (op = op') && Nat.beq a a' && Nat.beq b b' && Nat.beq c c' &&
      Nat.beq d d' && Nat.beq f f'
  | _, _ => false

def findNode (nodes : Certificate) (key : Node) : Option Nat :=
  match nodes.hints.lookup key.key with
  | none => none
  | some i => match nodes.nodes.lookup i with
    | none => none
    | some value => bif value.eqB key then some i else none


def certDom (nodes : Certificate) : Dom Nat where
  zero := 0
  applyOp op a b c d f :=
    if op=.logic .orr ∧ a=b then some a else findNode nodes (.app op a b c d f)


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

/-- Updating an existing key replaces its value instead of extending a history of writes. -/
def Tree.insert {α : Type} (key : Nat) (value : α) : Tree α → Tree α
  | .empty => .node key value .empty .empty
  | .node k v left right =>
    bif Nat.beq key k then .node k value left right
    else bif Nat.blt key k then .node k v (insert key value left) right
    else .node k v left (insert key value right)


/-- A sparse representation of the same functional environment. The initial
functions handle keys that have not been written. -/
structure FastEnv (α : Type) where
  initial : Env α
  regs : Tree α := .empty
  slots : Tree α := .empty
  carry : Option α


namespace FastEnv
variable {α : Type}

def ofEnv (e : Env α) : FastEnv α := ⟨e, .empty, .empty, e.carry⟩
def toEnv (e : FastEnv α) : Env α where
  reg r := (e.regs.lookup r.ctorIdx).orElse fun _ => e.initial.reg r
  slot off := (e.slots.lookup off).getD (e.initial.slot off)
  carry := e.carry


def setReg (e : FastEnv α) (d : Reg) (v : α) : FastEnv α :=
  { e with regs := e.regs.insert d.ctorIdx v }
def setSlot (e : FastEnv α) (off : Nat) (v : α) : FastEnv α :=
  { e with slots := e.slots.insert off v }
def withCarry (e : FastEnv α) (c : Option α) : FastEnv α := { e with carry := c }


def decodedStep (D : Dom α) (size : Nat) (e : FastEnv α) : Decoded → Option (FastEnv α)
  | .scalar op d a b c => do
    if d=.x0 || !op.valid then none else do
      let va ← arg D e.toEnv op.useA a
      let vb ← arg D e.toEnv op.useB b
      let vc ← arg D e.toEnv op.useC c
      let vd ← arg D e.toEnv op.useD d
      let cf ← carryArg D e.toEnv op
      let vr ← D.applyOp op va vb vc vd cf
      return (e.setReg d vr).withCarry (if op.flags then some vr else e.carry)
  | .load d off => if d=.x0 || !(off%8=0 && off+8≤size && off<32768) then none
      else some (e.setReg d (e.toEnv.slot off))
  | .store r off => if !(off%8=0 && off+8≤size && off<32768) then none
      else (e.toEnv.reg r).map (e.setSlot off)


def step (D : Dom α) (size : Nat) (e : FastEnv α) (i : Instr) : Option (FastEnv α) := do
  let view ← decode i
  decodedStep D size e view.val


def eval (D : Dom α) (size : Nat) : List Instr → FastEnv α → Option (FastEnv α)
  | [], e => some e
  | i :: is, e => (step D size e i).bind (eval D size is)


def data (e : FastEnv α) : Tree α × Tree α × Option α := (e.regs, e.slots, e.carry)


end FastEnv

def evalFast {α : Type} (D : Dom α) (size : Nat) (is : List Instr) (e : Env α) : Option (Env α) :=
  (FastEnv.eval D size is (FastEnv.ofEnv e)).map FastEnv.toEnv


/-- The finite part of a computed state can be materialized and checked once. -/
def evalData {α : Type} (D : Dom α) (size : Nat) (is : List Instr) (e : Env α) :
    Option (Tree α × Tree α × Option α) :=
  (FastEnv.eval D size is (FastEnv.ofEnv e)).map FastEnv.data


def fromData {α : Type} (e : Env α) (d : Tree α × Tree α × Option α) : Env α :=
  (FastEnv.mk e d.1 d.2.1 d.2.2).toEnv


end VG.Proof.Weierstrass.AArch64.Forward
