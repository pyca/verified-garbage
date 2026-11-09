module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldStep
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def fieldProgram (loc : Nat → Nat) : List PointOp → Prog isa
  | [] => .block []
  | op::ops => .seq (fieldCode loc op) (fieldProgram loc ops)

def fieldLive : List PointOp → List Nat → List Nat
  | [],V => V
  | op::ops,V => fieldLive ops (op.out::V)

def fieldReads : List PointOp → List Nat → Bool
  | [],_ => true
  | op::ops,V => op.ins.all (fun x => decide (x∈V)) && fieldReads ops (op.out::V)

def FieldProgramFrame (base : Addr) (loc : Nat → Nat) (ops : List PointOp) (m m' : Mem) : Prop :=
  ∀x,(∀op∈ops,ofs base x<loc op.out ∨ loc op.out+72≤ofs base x) →
    (ofs base x<3952 ∨ 4024≤ofs base x) → m' x=m x

theorem FieldPublic.trans {s t u : State} (h : FieldPublic s t) (k : FieldPublic t u) : FieldPublic s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr),k.sp.trans h.sp,k.rd.trans h.rd,k.wr.trans h.wr,k.v31.trans h.v31⟩

theorem field_program_ok {base : Addr} {W : Nat} {loc : Nat → Nat} {Sl : Nat → Prop}
    (hW : 4024≤W) (hMax : W≤8192) (layout : FieldLayout loc Sl)
    (ops : List PointOp) {s : State} {V : List Nat} {E : Nat → Fin fieldPrime}
    (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E (fun _ => 1) s)
    (live : ∀x∈V,Sl x) (slots : ∀op∈ops,∀x∈op.out::op.ins,Sl x)
    (reads : fieldReads ops V=true) (coeff : ∀op∈ops,fieldCoeffs op) :
    WP isa (fieldProgram loc ops) s fun t =>
      OrdinaryInv base fieldPrime loc (fieldLive ops V) (pointRun ops E) (fun _ => 1) t ∧
      Scr t base W ∧ FieldPublic s t ∧ FieldProgramFrame base loc ops s.mem t.mem := by
  induction ops generalizing s V E with
  | nil =>
    exact WP.block_nil ⟨inv,hs,⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩,fun _ _ _ => rfl⟩
  | cons op ops ih =>
    simp only [fieldReads,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at reads
    rw [fieldProgram,WP.seq_iff]
    refine WP.mono (field_step_ok hs hW hMax layout inv live op (slots op (by simp)) reads.1
      (coeff op (by simp))) fun u ⟨iu,hu,pu,fu⟩ => ?_
    refine WP.mono (ih hu iu (fun x hx => by
      rcases List.mem_cons.mp hx with rfl|hx
      · exact slots op (by simp) op.out (by simp)
      · exact live x hx)
      (fun q hq => slots q (List.mem_cons_of_mem _ hq)) reads.2
      (fun q hq => coeff q (List.mem_cons_of_mem _ hq))) fun t ⟨it,ht,pt,ft⟩ => ?_
    refine ⟨it,ht,pu.trans pt,?_⟩
    intro x hx scratch
    exact (ft x (fun q hq => hx q (List.mem_cons_of_mem _ hq)) scratch).trans
      (fu x (hx op (by simp)) scratch)

end VG.Proof.Weierstrass.AArch64.P521Native
