import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Domain
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Tree

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

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

theorem Node.eqB_eq_true (a b : Node) : a.eqB b = true ↔ a = b := by
  cases a <;> cases b <;> simp [Node.eqB, Bool.and_eq_true, Nat.beq_eq, and_assoc]

theorem findNode_eq {nodes : Certificate} {key : Node} {i : Nat}
    (h : findNode nodes key=some i) : nodes.nodes.lookup i=some key := by
  unfold findNode at h
  cases he : nodes.hints.lookup key.key with
  | none => simp only [he] at h; cases h
  | some j =>
    simp only [he] at h
    cases hv : nodes.nodes.lookup j with
    | none => simp only [hv] at h; cases h
    | some value =>
      simp only [hv, cond_eq_ite] at h
      split at h
      · rename_i heq
        cases h
        rw [(Node.eqB_eq_true _ _).mp heq] at hv
        exact hv
      · cases h

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
