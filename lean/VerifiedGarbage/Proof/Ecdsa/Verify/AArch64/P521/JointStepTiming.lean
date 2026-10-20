module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Public generator inputs retained throughout the joint loop. -/
structure GeneratorInput (C : Curve) (base T : Addr) (G : Point C) (u : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 bytes : ∀j<577,s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j
 one : tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1

theorem GeneratorInput.rebase {C : Curve} {base T : Addr} {G : Point C} {u : Nat} {s t : State}
 (h : GeneratorInput C base T G u s)
 (hu : Unch base (winW P521Joint.K++cacheW P521Joint.K) s.mem t.mem)
 (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hy : t.syms=s.syms) :
 GeneratorInput C base T G u t := by
 refine ⟨h.source.unch hu (by decide) hr hw hy,?_,?_⟩
 · intro j hj
   rw [hu.byte (by intro w hw; have ha:=generator_apart w hw; omega)
    (by change 3304+j<2^64; omega)]
   exact h.bytes j hj
 · unfold tmv
   rw [hu.wordsVal (by decide) (by decide)]
   exact h.one

theorem GeneratorInput.current {C : Curve} {base T : Addr} {G P A : Point C} {u j : Nat} {s₀ s : State}
 (h : GeneratorInput C base T G u s₀) (hj : j<577) (sy : s.syms=s₀.syms)
 (hs : JointDigitPost P521Joint.K C base 8192 P s₀ s j A) :
 FixedDigitInput C base T G u j s ∧ tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1 := by
 refine ⟨⟨h.source.unch hs.st.unch (by decide) hs.st.keep.rd hs.st.keep.wr sy,hs.x19,?_⟩,?_⟩
 · rw [hs.st.unch.byte (by
     intro w hw
     have ha:=generator_apart w (List.mem_append_left _ hw)
     omega) (by change 3304+j<2^64; omega)]
   exact h.bytes j hj
 · unfold tmv
   rw [hs.st.unch.wordsVal (by decide) (by decide)]
   exact h.one

def JointRelation (C : Curve) (base : Addr) (P G : Point C) (u v j : Nat) (s₀ t₀ s t : State) : Prop :=
 (∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (loopLive P521Joint.K) E s t) ∧
 JointDigitPost P521Joint.K C base 8192 P s₀ s j (jointPoint G P u v j) ∧
 JointDigitPost P521Joint.K C base 8192 P t₀ t j (jointPoint G P u v j) ∧
 s.syms=s₀.syms ∧ t.syms=t₀.syms

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
  | seq ds es => cases es with
    | seq dbs es => cases es with
      | seq ps gs =>
       cases et with
       | seq dt et => cases et with
         | seq dbt et => cases et with
           | seq pt gt =>
            have eps : Exec isa (PubNaf.step P521Joint.K) _ _ _ := .seq ds (.seq dbs ps)
            have ept : Exec isa (PubNaf.step P521Joint.K) _ _ _ := .seq dt (.seq dbt pt)
            obtain ⟨he,E,hpair⟩:=stepRaw_relCT hL hp hone checks hF₁ hF₂ (j:=j) (by change j<577; omega)
             _ _ _ _ _ _ ⟨pair,hs.st,ht.st,hs.cache,ht.cache,hs.x19,ht.x19⟩ eps ept
            have hcA:=jointPoint_curve hC hG hP u v (j+1)
            obtain ⟨_,_,e1,h1⟩:=peerStep_ok hL hp hC hM3 hone hP hcA hF₁ hj hs
            obtain ⟨_,_,e2,h2⟩:=peerStep_ok hL hp hC hM3 hone hP hcA hF₂ hj ht
            obtain ⟨_,rfl⟩:=Exec.det eps e1
            obtain ⟨_,rfl⟩:=Exec.det ept e2
            have a:=g₁.current (by omega) ((Exec.syms eps).trans sys) h1
            have b:=g₂.current (by omega) ((Exec.syms ept).trans syt) h2
            have ev : E (p521.sl ONEP)=1 := by
             rw [←hpair.left.val _ (by decide)]
             exact a.2
            obtain ⟨hg,res⟩:=fixedDigit_relCT hL hC hp hone ev (by omega) mixed
             _ _ _ _ _ _ ⟨hpair,a.1,b.1⟩ gs gt
            exact ⟨by simpa only [List.append_assoc] using congrArg₂ (·++·) he hg,res⟩
 exact ⟨result.1,result.2,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
