module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
import VerifiedGarbage.Proof.Bignum.Arm.CombExpControl
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CombExp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
meta import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
import VerifiedGarbage.Proof.Bignum.Arm.CombExpStep
meta import VerifiedGarbage.Proof.Bignum.Arm.CombExpStep

/-! Every comb row performs one square, one full scan, and one product. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (Operand)

private theorem operand (q : Nat) (h : q=1 ∨ q=6) : Operand q := by
  rcases h with rfl | rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]

private theorem squareRow_ok {base source table : BitVec 32} {len w bytes N M g E i : Nat}
    {P : State→Prop} {regions : List Region} (A : TwoExp.Montgomery base len w P regions)
    (s : State) (h : RowInput base source table len w bytes N M g E i P s) :
    WP isa (A.op 6 6 6) s (RowInput base source table len w bytes N M g (2*E) i P) := by
  refine WP.mono (square_ok A s h.power h.persistent) ?_
  rintro t ⟨power,p,header,_,_⟩
  exact ⟨power,p,h.controls.after_header header,(header 192 (by decide)).trans h.counter⟩

private theorem chosen_ok {base source table : BitVec 32} {len w bytes N M g x E i : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (hi : i<Spec.Rsa.FixedBaseComb.rows N)
    (s : State) (h : RowInput base source table len w bytes N M g E i P s) :
    WP isa VG.Impl.Bignum.Arm.CombExp.choose s (SelectedInput base source table len w bytes N M g E i P) := by
  refine WP.mono (K.choose_ok s i E hi h.power h.persistent h.controls h.counter) ?_
  rintro t ⟨power,p,controls,counter,bound,_,_,_⟩
  exact ⟨⟨power,p,controls,counter⟩,bound⟩

theorem step_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 E1 E2 i : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) (ct : Timing K1 K2)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N) :
    RelCT isa (fun s t => RowInput base source table len w bytes N M g E1 i P1 s ∧
      RowInput base source table len w bytes N M g E2 i P2 t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.step K1.arithmetic.op) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombExp.step
  refine relCT_chain
    ((ct.op_ct 6 6 6 (operand 6 (by simp)) (operand 6 (by simp)) (operand 6 (by simp))).mono
      (fun _ _ h => ⟨⟨h.1.power.ready,h.1.persistent,by rw [h.1.power.modulus]; exact h.1.power.bound⟩,
        ⟨h.2.1.power.ready,h.2.1.persistent,by rw [h.2.1.power.modulus]; exact h.2.1.power.bound⟩,h.2.2⟩)
      (fun _ _ h => h))
    (fun s h => squareRow_ok K1.arithmetic s h)
    (fun s h => by simpa only [ct.same] using squareRow_ok K2.arithmetic s h) ?_
  exact relCT_chain (ct.choose_ct i (2*E1) (2*E2) hi)
    (fun s h => chosen_ok K1 hi s h) (fun s h => chosen_ok K2 hi s h)
    ((ct.op_ct 6 6 1 (operand 6 (by simp)) (operand 6 (by simp)) (operand 1 (by simp))).mono
      (fun _ _ h => ⟨⟨h.1.power.ready,h.1.persistent,by rw [h.1.power.modulus]; exact h.1.selectedBound⟩,
        ⟨h.2.1.power.ready,h.2.1.persistent,by rw [h.2.1.power.modulus]; exact h.2.1.selectedBound⟩,h.2.2⟩)
      (fun _ _ h => h))

private theorem next_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombExp.next) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

theorem round_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 i : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) (ct : Timing K1 K2)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N) :
    RelCT isa (fun s t => RowInput base source table len w bytes N M g
      (VG.Proof.Rsa.FixedBaseComb.high N x1 (i+1)) i P1 s ∧
      RowInput base source table len w bytes N M g (VG.Proof.Rsa.FixedBaseComb.high N x2 (i+1)) i P2 t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.round K1.arithmetic.op) (fun _ _ => True) := by
  have wp1 (s : State) (h : RowInput base source table len w bytes N M g
      (VG.Proof.Rsa.FixedBaseComb.high N x1 (i+1)) i P1 s) :=
    WP.mono (row_ok K1 s hi h.power h.persistent h.controls h.counter) fun _ k => k.1.ready.ptr
  have wp2 (s : State) (h : RowInput base source table len w bytes N M g
      (VG.Proof.Rsa.FixedBaseComb.high N x2 (i+1)) i P2 s) :
      WP isa (VG.Impl.Bignum.Arm.CombExp.step K1.arithmetic.op) s fun t => t.gpr .r0=base := by
    simpa only [ct.same,VG.Impl.Bignum.Arm.CombExp.step] using WP.mono (row_ok K2 s hi h.power h.persistent h.controls h.counter) fun _ k => k.1.ready.ptr
  unfold VG.Impl.Bignum.Arm.CombExp.round
  exact relCT_chain (step_ct K1 K2 ct hi) wp1 wp2
    (next_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

end VG.Proof.Bignum.Arm.CombExp
