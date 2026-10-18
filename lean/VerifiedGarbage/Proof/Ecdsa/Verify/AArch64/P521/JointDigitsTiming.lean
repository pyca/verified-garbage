module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointStepTiming
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

theorem jointDigits_relCT {C : Curve} {base T : Addr} {P G A : Point C} {s₀ t₀ : State} {u v j : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hA : onCurve C A=true)
 (hF₁ : NafFixed P521Joint.K C base s₀ P v) (hF₂ : NafFixed P521Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : DigitChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D)
 (hj : j<577) :
 RelCT isa (fun s t=>
  (∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (digitLive P521Joint.K) E s t) ∧
  JointDoublePost P521Joint.K C base 8192 P s₀ s j A ∧
  JointDoublePost P521Joint.K C base 8192 P t₀ t j A ∧ s.syms=s₀.syms ∧ t.syms=t₀.syms)
 P521Joint.digits (fun s t=>
  (∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (loopLive P521Joint.K) E s t) ∧
  JointDigitPost P521Joint.K C base 8192 P s₀ s j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 7 u j)) ∧
  JointDigitPost P521Joint.K C base 8192 P t₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 7 u j)) ∧
  s.syms=s₀.syms ∧ t.syms=t₀.syms) := by
 intro s t ts tt s' t' ⟨⟨E,pair⟩,hs,ht,sys,syt⟩ es et
 have fs:=fixedStep_of_source hL hp hC hM3 hone hG hF₁ g₁.source g₁.bytes g₁.one
 have ft:=fixedStep_of_source hL hp hC hM3 hone hG hF₂ g₂.source g₂.bytes g₂.one
 obtain ⟨_,_,exs,postS⟩:=digits_ok hL hp hC hM3 hone hP hA hF₁ fs hj sys hs
 obtain ⟨_,_,ext,postT⟩:=digits_ok hL hp hC hM3 hone hP hA hF₂ ft hj syt ht
 obtain ⟨_,rfl⟩:=Exec.det es exs
 obtain ⟨_,rfl⟩:=Exec.det et ext
 have result : ts=tt ∧ ∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K)
   (loopLive P521Joint.K) E s' t' := by
  cases es with
  | seq ps gs => cases et with
    | seq pt gt =>
     obtain ⟨he,E',hpair⟩:=digit_relCT hL hp hone checks hF₁ hF₂ hj
      _ _ _ _ _ _ ⟨pair,hs.st,ht.st,hs.cache,ht.cache,hs.x19,ht.x19⟩ ps pt
     obtain ⟨_,_,e1,h1⟩:=jointDigit_ok hL hp hC hM3 hone hP hA hs.st hF₁ hs.cache hj hs.x19 hs.dlt hs.d
     obtain ⟨_,_,e2,h2⟩:=jointDigit_ok hL hp hC hM3 hone hP hA ht.st hF₂ ht.cache hj ht.x19 ht.dlt ht.d
     obtain ⟨_,rfl⟩:=Exec.det ps e1
     obtain ⟨_,rfl⟩:=Exec.det pt e2
     have a:=g₁.current hj ((Exec.syms ps).trans sys) h1
     have b:=g₂.current hj ((Exec.syms pt).trans syt) h2
     have pair' : FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K)
       (loopLive P521Joint.K) E' _ _ := hpair.sub (by decide)
     have ev : E' (p521.sl ONEP)=1 := by
      rw [←pair'.left.val _ (by decide)]
      exact a.2
     obtain ⟨hg,res⟩:=fixedDigit_relCT hL hC hp hone ev hj mixed
      _ _ _ _ _ _ ⟨pair',a.1,b.1⟩ gs gt
     exact ⟨by rw [he,hg],res⟩
 exact ⟨result.1,result.2,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
