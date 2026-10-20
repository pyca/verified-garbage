module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpControl
import VerifiedGarbage.Proof.Bignum.Arm.CombExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpLoop
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming

/-! The public number of remaining comb rows controls every back edge. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

structure LoopInput (base source table : BitVec 32) (len w bytes N M g x k : Nat)
    (P : State→Prop) (s : State) : Prop where
  power : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x k) s
  persistent : P s
  controls : Controls base source table bytes N s
  counter : Counter base k s

theorem rows_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 count : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) (ct : Timing K1 K2)
    (positive : 0<count) (bound : count≤Spec.Rsa.FixedBaseComb.rows N) (fits : count<2^32) :
    RelCT isa (fun s t => LoopInput base source table len w bytes N M g x1 count P1 s ∧
      LoopInput base source table len w bytes N M g x2 count P2 t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.rows K1.arithmetic.op) (fun _ _ => True) := by
  let I := fun k s t => 0<k ∧ k≤Spec.Rsa.FixedBaseComb.rows N ∧ k<2^32 ∧
    LoopInput base source table len w bytes N M g x1 k P1 s ∧
    LoopInput base source table len w bytes N M g x2 k P2 t ∧ s.sp=t.sp
  have step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.CombExp.round K1.arithmetic.op) fun u v =>
      isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
      (isa.eval .ne u=some true → ∃ m<k, I m u v) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨positiveK,boundK,fitsK,left,right,sp⟩ := h
    have successor : k-1+1=k := by omega
    have timing := relCT_keep_sp (round_ct K1 K2 ct (i:=k-1) (by omega)) (fun _ _ h => h.2.2)
    have leftInput : RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x1 (k-1+1)) (k-1) P1 s := by
      simpa only [successor] using (show RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x1 k) (k-1) P1 s from
        ⟨left.power,left.persistent,left.controls,by simpa only [successor] using left.counter⟩)
    have rightInput : RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x2 (k-1+1)) (k-1) P2 t := by
      simpa only [successor] using (show RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x2 k) (k-1) P2 t from
        ⟨right.power,right.persistent,right.controls,by simpa only [successor] using right.counter⟩)
    obtain ⟨trace,sp'⟩ := timing s t tr1 tr2 u v ⟨leftInput,rightInput,sp⟩ e1 e2
    have correct1 := round_ok K1 s (i:=k-1) (by omega) (by omega) leftInput.power leftInput.persistent
      leftInput.controls leftInput.counter
    have correct2 := round_ok K2 t (i:=k-1) (by omega) (by omega) rightInput.power rightInput.persistent
      rightInput.controls rightInput.counter
    rw [←ct.same] at correct2
    obtain ⟨_,_,run1,power1,p1,controls1,counter1,zero1,_,_⟩ := correct1
    obtain ⟨_,_,run2,power2,p2,controls2,counter2,zero2,_,_⟩ := correct2
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [zero1,zero2]
    · intro again
      have nonzero : k-1≠0 := by
        intro zero
        change some (!u.z)=some true at again
        simp only [zero1,zero,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega,by omega,by omega,by omega,
        ⟨power1,p1,controls1,counter1⟩,⟨power2,p2,controls2,counter2⟩,sp'⟩
  unfold VG.Impl.Bignum.Arm.CombExp.rows
  exact (RelCT.loop I step count).mono
    (fun _ _ h => ⟨positive,bound,fits,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.CombExp
