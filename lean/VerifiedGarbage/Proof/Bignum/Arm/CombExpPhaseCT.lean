module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitial
import VerifiedGarbage.Proof.Bignum.Arm.CombExpLoop

import VerifiedGarbage.Proof.Bignum.Arm.CombExpLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitialCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpPhase
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel

/-! Cached comb exponentiation reveals the fixed public row count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Spec.Rsa.Mont (numAt Operand)

structure PhaseInput (base source table : BitVec 32) (len w bytes N M : Nat)
    (P : State→Prop) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  persistent : P s
  controls : Controls base source table bytes N s
  modulus : numAt s.mem (State.addr base) w 0=M
  r2 : numAt s.mem (State.addr base) w 4=2^(128*w)%M

private theorem initialInput_ok {base source table : BitVec 32} {len w bytes N M g x : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (odd : M%2=1)
    (s : State) (h : PhaseInput base source table len w bytes N M P s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.initial K.arithmetic.op) s
      (LoopInput base source table len w bytes N M g x (Spec.Rsa.FixedBaseComb.rows N) P) := by
  refine WP.mono (initial_ok (g:=g) K.arithmetic s h.ready h.persistent h.controls h.modulus odd h.r2) ?_
  rintro t ⟨power,p,controls,counter,_,_⟩
  exact ⟨by simpa only [VG.Proof.Rsa.FixedBaseComb.high_top] using power,p,controls,counter⟩

private theorem rowsInput_ok {base source table : BitVec 32} {len w bytes N M g x : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows N) (fits : Spec.Rsa.FixedBaseComb.rows N<2^32)
    (s : State) (h : LoopInput base source table len w bytes N M g x (Spec.Rsa.FixedBaseComb.rows N) P s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.rows K.arithmetic.op) s (TwoExp.OpInput base len w P 7) := by
  refine WP.mono (rows_ok K s positive (Nat.le_refl _) fits h.power h.persistent h.controls h.counter) ?_
  rintro t ⟨power,p,_,_,_,_⟩
  exact ⟨power.ready,p,by rw [power.one]; exact power.ready.modulus⟩

theorem phase_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) (ct : Timing K1 K2)
    (odd : M%2=1) (positive : 0<Spec.Rsa.FixedBaseComb.rows N) (fits : Spec.Rsa.FixedBaseComb.rows N<2^32) :
    RelCT isa (fun s t => PhaseInput base source table len w bytes N M P1 s ∧
      PhaseInput base source table len w bytes N M P2 t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.phase K1.arithmetic.op) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombExp.phase
  refine relCT_chain ((initial_ct K1 K2 ct).mono
    (fun _ _ h => ⟨⟨h.1.ready,h.1.persistent⟩,⟨h.2.1.ready,h.2.1.persistent⟩,h.2.2⟩) (fun _ _ h => h))
    (fun s h => initialInput_ok K1 odd s h)
    (fun s h => by simpa only [ct.same] using initialInput_ok K2 odd s h) ?_
  exact relCT_chain (rows_ct K1 K2 ct positive (Nat.le_refl _) fits)
    (fun s h => rowsInput_ok K1 positive fits s h)
    (fun s h => by simpa only [ct.same] using rowsInput_ok K2 positive fits s h)
    (ct.op_ct 6 6 7
      (by simp [Operand,Spec.Rsa.Mont.aAcc,Spec.Rsa.Mont.aTmp])
      (by simp [Operand,Spec.Rsa.Mont.aAcc,Spec.Rsa.Mont.aTmp])
      (by simp [Operand,Spec.Rsa.Mont.aAcc,Spec.Rsa.Mont.aTmp]))

end VG.Proof.Bignum.Arm.CombExp
