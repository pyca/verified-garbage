module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitCall

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointStepTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
import VerifiedGarbage.Proof.Framework.AArch64.Syms

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

theorem jointDigitsBody_relCT {C : Curve} {base T : Addr} {P G A : Point C} {s₀ t₀ : State} {u v j : Nat}
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
 P521Joint.digitsBody (fun s t=>
  (∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (loopLive P521Joint.K) E s t) ∧
  JointDigitPost P521Joint.K C base 8192 P s₀ s j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 7 u j)) ∧
  JointDigitPost P521Joint.K C base 8192 P t₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 7 u j)) ∧
  s.syms=s₀.syms ∧ t.syms=t₀.syms) := by
 intro s t ts tt s' t' ⟨⟨E,pair⟩,hs,ht,sys,syt⟩ es et
 have fs:=fixedStep_of_source hL hp hC hM3 hone hG hF₁ g₁.source g₁.bytes g₁.one
 have ft:=fixedStep_of_source hL hp hC hM3 hone hG hF₂ g₂.source g₂.bytes g₂.one
 obtain ⟨_,_,exs,postS⟩:=digitsBody_ok hL hp hC hM3 hone hP hA hF₁ fs hj sys hs
 obtain ⟨_,_,ext,postT⟩:=digitsBody_ok hL hp hC hM3 hone hP hA hF₂ ft hj syt ht
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
 have hf₁ : NafFixed P521Joint.K C base (digitOrigin s₀ s) P v := ⟨hF₁.ro_lt,hF₁.zero,hF₁.pt,hF₁.digits⟩
 have hf₂ : NafFixed P521Joint.K C base (digitOrigin t₀ t) P v := ⟨hF₂.ro_lt,hF₂.zero,hF₂.pt,hF₂.digits⟩
 have gg₁ : GeneratorInput C base T G u (digitOrigin s₀ s) := g₁.rebase (Unch.refl _ _ _) rfl rfl rfl
 have gg₂ : GeneratorInput C base T G u (digitOrigin t₀ t) := g₂.rebase (Unch.refl _ _ _) rfl rfl rfl
 obtain ⟨he,a,b,hq,rfl,rfl⟩ := callDigits_relCT "vg_ecdsa_p521_verify_digits"
   (jointDigitsBody_relCT hL hp hC hM3 hone hP hG hA hf₁ hf₂ gg₁ gg₂ checks mixed hj)
   _ _ _ _ _ _ (show _ from ⟨⟨E,pair.digitSaved⟩,
     digitCall_pre (by intro r; cases r <;> decide) hs,
     digitCall_pre (by intro r; cases r <;> decide) ht,sys,syt⟩) es et
 obtain ⟨E',pair'⟩ := hq.1
 exact ⟨he,⟨E',pair'.digitRestored⟩,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩

theorem jointStep_relCT {C : Curve} {base T : Addr} {P G : Point C} {s₀ t₀ : State} {u v j : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF₁ : NafFixed P521Joint.K C base s₀ P v) (hF₂ : NafFixed P521Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : StepChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D)
 (hj : j<576) :
 RelCT isa (JointRelation C base P G u v (j+1) s₀ t₀) P521Joint.step
  (JointRelation C base P G u v j s₀ t₀) := by
 intro s t ts tt s' t' ⟨pair,hs,ht,sys,syt⟩ es et
 have fs:=fixedStep_of_source hL hp hC hM3 hone hG hF₁ g₁.source g₁.bytes g₁.one
 have ft:=fixedStep_of_source hL hp hC hM3 hone hG hF₂ g₂.source g₂.bytes g₂.one
 obtain ⟨_,_,exs,postS⟩:=step_ok hL hp hC hM3 hone hP hG hF₁ fs hj sys hs
 obtain ⟨_,_,ext,postT⟩:=step_ok hL hp hC hM3 hone hP hG hF₂ ft hj syt ht
 obtain ⟨_,rfl⟩:=Exec.det es exs
 obtain ⟨_,rfl⟩:=Exec.det et ext
 have result : ts=tt ∧ ∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K)
   (loopLive P521Joint.K) E s' t' := by
  cases es with
  | seq ds rest => cases rest with
    | seq dbs gs => cases et with
      | seq dt rest => cases rest with
        | seq dbt gt =>
          have eps := Exec.seq ds dbs
          have ept := Exec.seq dt dbt
          have hcA := jointPoint_curve hC hG hP u v (j+1)
          obtain ⟨_,_,e1,h1⟩ := jointDoubleBy_ok hL hC hM3 hF₁ hcA (dbl_spec hL hp) (by change j<577; omega_using [hj]) hs
          obtain ⟨_,_,e2,h2⟩ := jointDoubleBy_ok hL hC hM3 hF₂ hcA (dbl_spec hL hp) (by change j<577; omega_using [hj]) ht
          obtain ⟨_,rfl⟩ := Exec.det eps e1
          obtain ⟨_,rfl⟩ := Exec.det ept e2
          obtain ⟨he,⟨E',pair'⟩,_⟩ := doubleDRaw_relCT hL checks (dbl_spec hL hp) double_ct (j:=j) (by change j<577; omega_using [hj])
            _ _ _ _ _ _ ⟨pair,hs.st,ht.st,hs.cache,ht.cache,hs.x19,ht.x19⟩ eps ept
          obtain ⟨hg,⟨E'',pair''⟩,_⟩ := jointDigits_relCT hL hp hC hM3 hone hP hG (hC.onCurve_add hcA hcA)
            hF₁ hF₂ g₁ g₂ checks.digit mixed (by omega_using [hj])
            _ _ _ _ _ _ ⟨⟨E',pair'⟩,h1,h2,(Exec.syms eps).trans sys,(Exec.syms ept).trans syt⟩ gs gt
          exact ⟨by simpa only [List.append_assoc] using congr (congrArg HAppend.hAppend he) hg,E'',pair''⟩
 exact ⟨result.1,result.2,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
