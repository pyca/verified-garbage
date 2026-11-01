module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.CombExp

/-! Montgomery one and public row-count initialization use a fixed trace. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

private theorem op (q : Nat) (h : q=4 ∨ q=6 ∨ q=7) : Operand q := by
  rcases h with rfl|rfl|rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]

theorem initial_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2)
    (timing : Timing K1 K2) :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ P1 s) ∧
      (ArithmeticReady base len w t ∧ P2 t) ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.initial K1.arithmetic.op) (fun _ _ => True) := by
  have one {P : State→Prop} {regions : List Region}
      (A : TwoExp.Montgomery base len w P regions) (s : State)
      (h : ArithmeticReady base len w s ∧ P s) :
      WP isa (smallConst 7 1) s (TwoExp.OpInput base len w P 7) := by
    refine WP.mono (smallConst_ok s 1 h.1 (o := 7)
      (by decide) (by decide) (by decide) (by decide)) ?_
    rintro u ⟨ready,one,_zero,_keeps,frame,rest⟩
    refine ⟨ready,A.stable frame rest h.2,?_⟩
    change numAt u.mem (State.addr base) w 7=1 at one
    rw [one]
    exact ready.modulus
  have product {P : State→Prop} {regions : List Region}
      (A : TwoExp.Montgomery base len w P regions) (s : State)
      (h : TwoExp.OpInput base len w P 7 s) :
      WP isa (A.op 6 4 7) s fun t => t.gpr .r0=base := by
    exact WP.mono (A.op_ok s 6 4 7 h.1 h.2.1 (op 6 (by simp)) (op 4 (by simp)) (op 7 (by simp))
      (by decide) h.2.2) fun _ post => post.1.ptr
  unfold VG.Impl.Bignum.Arm.CombExp.initial
  refine relCT_chain ((smallConst_ct (base := base) (len := len) (w := w) (o := 7) 1
    (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1,h.2.1.1,h.2.2⟩) (fun _ _ h => h))
    (one K1.arithmetic) (one K2.arithmetic) ?_
  refine relCT_chain (Q₂ := fun t => t.gpr .r0=base) (timing.op_ct 6 4 7 (op 6 (by simp)) (op 4 (by simp)) (op 7 (by simp)))
    (product K1.arithmetic) (fun s h => ?_) ?_
  · rw [timing.same]
    exact product K2.arithmetic s h
  · apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.1.symm

end VG.Proof.Bignum.Arm.CombExp
