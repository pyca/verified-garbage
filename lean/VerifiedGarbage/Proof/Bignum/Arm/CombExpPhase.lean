module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpLoop
import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitial
import VerifiedGarbage.Proof.Bignum.Arm.CombExpFinish
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel

/-! The public comb schedule computes the same full scalar power as direct exponentiation. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem phase_ok {base source table : BitVec 32} {len w bytes N M g x : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (s : State)
    (ready : ArithmeticReady base len w s) (hp : P s) (controls : Controls base source table bytes N s)
    (modulus : numAt s.mem (State.addr base) w 0=M) (odd : M%2=1)
    (r2 : numAt s.mem (State.addr base) w 4=2^(128*w)%M)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows N) (fits : Spec.Rsa.FixedBaseComb.rows N<2^32)
    (bound : x<2^N) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.phase K.arithmetic.op) s fun t =>
      ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 6=Spec.Rsa.powMod g x M ∧
      numAt t.mem (State.addr base) w 0=M ∧ numAt t.mem (State.addr base) w 4=2^(128*w)%M ∧
      numAt t.mem (State.addr base) w 7=1 ∧ P t ∧ Controls base source table bytes N t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.CombExp.phase,WP.seq_iff]
  refine WP.mono (initial_ok (g:=g) K.arithmetic s ready hp controls modulus odd r2) ?_
  rintro u ⟨powerU,pu,controlsU,counterU,frameU,restU⟩
  have start : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x (Spec.Rsa.FixedBaseComb.rows N)) u := by
    simpa only [VG.Proof.Rsa.FixedBaseComb.high_top] using powerU
  rw [WP.seq_iff]
  refine WP.mono (rows_ok K u positive (Nat.le_refl _) fits start pu controlsU counterU) ?_
  rintro v ⟨powerV,pv,controlsV,_,frameV,restV⟩
  rw [VG.Proof.Rsa.FixedBaseComb.high_zero N x bound] at powerV
  refine WP.mono (finish_ok K.arithmetic v powerV pv) ?_
  rintro t ⟨readyT,resultT,modT,r2T,oneT,pt,headerT,frameT,restT⟩
  exact ⟨readyT,resultT,modT,r2T,oneT,pt,controlsV.after_header headerT,
    frameU.trans (frameV.trans frameT),restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.CombExp
