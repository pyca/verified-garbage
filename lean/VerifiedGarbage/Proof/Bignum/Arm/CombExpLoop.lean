module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpControl
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel

/-! Public descending rows implement the fixed-base comb Horner recurrence. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem rows_ok {base source table : BitVec 32} {len w bytes N M g x count : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (s : State)
    (positive : 0<count) (bound : count≤Spec.Rsa.FixedBaseComb.rows N)
    (fits : Spec.Rsa.FixedBaseComb.rows N<2^32)
    (h : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x count) s)
    (hp : P s) (controls : Controls base source table bytes N s) (counter : Counter base count s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.rows K.arithmetic.op) s fun t =>
      Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x 0) t ∧ P t ∧
      Controls base source table bytes N t ∧ Counter base 0 t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => 0<k ∧ k≤Spec.Rsa.FixedBaseComb.rows N ∧
    Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x k) t ∧ P t ∧
    Controls base source table bytes N t ∧ Counter base k t ∧
    Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold VG.Impl.Bignum.Arm.CombExp.rows
  refine WP.loop (M:=isa) I ?_ count s
    ⟨positive,bound,h,hp,controls,counter,Frame.refl _ _,Rest.refl _ _⟩
  intro k t inv
  obtain ⟨hk,le,power,pt,control,counted,frame,rest⟩ := inv
  have split : k-1+1=k := by omega
  refine WP.mono (round_ok K t (i:=k-1) (by omega) (by omega)
    (by simpa only [split] using power) pt control (by simpa only [split] using counted)) ?_
  rintro u ⟨powerU,pu,controlsU,counterU,zero,frameU,restU⟩
  by_cases last : k-1=0
  · left
    refine ⟨?_,?_,pu,controlsU,?_,frame.trans frameU,rest.trans restU⟩
    · change some (!u.z)=some false
      simp only [zero,last,decide_true,Bool.not_true]
    · simpa only [last] using powerU
    · simpa only [last] using counterU
  · right
    refine ⟨?_,k-1,by omega,by omega,by omega,powerU,pu,controlsU,counterU,
      frame.trans frameU,rest.trans restU⟩
    change some (!u.z)=some true
    simp only [zero,last,decide_false,Bool.not_false]

end VG.Proof.Bignum.Arm.CombExp
