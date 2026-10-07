import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Domain
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Tree

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

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

def nodeVal (nodes : Certificate) (input : Nat → BitVec 64) (i : Nat) : BitVec 64 × Bool :=
  match nodes.nodes.lookup i with
  | some (.input off) => (input off,false)
  | some (.app op a b c d f) =>
    if _hb : a<i ∧ b<i ∧ c<i ∧ d<i ∧ f<i then
      op.eval (nodeVal nodes input a).1 (nodeVal nodes input b).1
        (nodeVal nodes input c).1 (nodeVal nodes input d).1 (nodeVal nodes input f).2
    else (0,false)
  | _ => (0,false)
termination_by i

def findNode (nodes : Certificate) (key : Node) : Option Nat :=
  match nodes.hints.lookup key.key with
  | none => none
  | some i => if nodes.nodes.lookup i=some key then some i else none

theorem findNode_eq {nodes : Certificate} {key : Node} {i : Nat}
    (h : findNode nodes key=some i) : nodes.nodes.lookup i=some key := by
  unfold findNode at h
  cases he : nodes.hints.lookup key.key with
  | none => simp only [he] at h; cases h
  | some j =>
    simp only [he] at h
    split at h
    · cases h; assumption
    · cases h

def certDom (nodes : Certificate) : Dom Nat where
  zero := 0
  applyOp op a b c d f :=
    if op=.logic .orr ∧ a=b then some a else findNode nodes (.app op a b c d f)

theorem eval_copy (a : BitVec 64) (c d : BitVec 64) (f : Bool) :
    (Op.logic .orr).eval a a c d f=(a,false) := by
  simp [Op.eval,Op.useA,Op.useB,Op.useC,Op.useD,Op.useCarry,scalarState,Op.instr,exec,
    State.read,State.write,Size.bits,BitVec.setWidth_eq]

theorem certDom_sound {nodes : Certificate} (hv : CertValid nodes) (input : Nat → BitVec 64) :
    (certDom nodes).Sound (nodeVal nodes input) := by
  constructor
  · rw [show (certDom nodes).zero=0 from rfl,nodeVal,hv.1]
    exact ⟨rfl,rfl⟩
  · intro op a b c d f r hr
    change (if op=.logic .orr ∧ a=b then some a else findNode nodes (.app op a b c d f))=some r at hr
    split at hr
    · rename_i hc
      obtain ⟨rfl,rfl⟩ := hc
      cases hr
      rw [eval_copy]
      exact ⟨rfl,by intro h; cases h⟩
    · have hn := findNode_eq hr
      have hb := of_decide_eq_true (Tree.lookup_all hv.2 hn)
      change a<r ∧ b<r ∧ c<r ∧ d<r ∧ f<r at hb
      have he : nodeVal nodes input r=op.eval (nodeVal nodes input a).1
          (nodeVal nodes input b).1 (nodeVal nodes input c).1 (nodeVal nodes input d).1
          (nodeVal nodes input f).2 := by rw [nodeVal]; simp [hn,hb]
      exact ⟨congrArg Prod.fst he,fun _ => congrArg Prod.snd he⟩

end VG.Proof.Weierstrass.AArch64.Forward
