module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointStepTiming
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)
open Spec.Weierstrass

theorem jointLoop_relCT {C : Curve} {base T : Addr} {P G : Point C} {s₀ t₀ : State} {u v : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF₁ : NafFixed P521Joint.K C base s₀ P v) (hF₂ : NafFixed P521Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : StepChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D) :
 RelCT isa (JointRelation C base P G u v 576 s₀ t₀)
  (.loop P521Joint.step (.nonzero .x .x19)) (JointRelation C base P G u v 0 s₀ t₀) := by
 let I := fun j s t=>1≤j ∧ j≤576 ∧ JointRelation C base P G u v j s₀ t₀ s t
 have step : ∀j,RelCT isa (I j) P521Joint.step (fun s t=>
   eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
   (eval (.nonzero .x .x19) s=some false → JointRelation C base P G u v 0 s₀ t₀ s t) ∧
   (eval (.nonzero .x .x19) s=some true → ∃n<j,I n s t)) := by
  intro j
  by_cases hj : 1≤j
  · by_cases hn : j≤576
    · have e : j-1+1=j := by omega
      refine (jointStep_relCT hL hp hC hM3 hone hP hG hF₁ hF₂ g₁ g₂ checks mixed
       (j:=j-1) (by omega)).mono (P':=I j) (fun _ _ h=>by rw [e]; exact h.2.2) ?_
      intro s t h
      have xs:=h.2.1.x19
      have xt:=h.2.2.1.x19
      refine ⟨by simp only [eval,State.read,xs,xt],fun he=>?_,fun he=>?_⟩
      · have hz : j-1=0 := by
         by_contra hz
         have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
          rw [bne_iff_ne]
          intro hh
          have hh':=congrArg BitVec.toNat hh
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
          exact hz hh'
         have ht : eval (.nonzero .x .x19) s=some true := by
          change some (s.read .x .x19 != 0)=some true
          rw [read_x,xs,hb]
         rw [ht] at he
         cases he
        simpa only [hz] using h
      · have hz : j-1≠0 := by
         intro hz
         simp only [eval,State.read,xs,hz] at he
         cases he
        exact ⟨j-1,by omega,by omega,by omega,h⟩
    · exact RelCT.of_false (fun _ _ h=>hn h.2.1)
  · exact RelCT.of_false (fun _ _ h=>hj h.1)
 exact (RelCT.loop I step 576).mono (fun _ _ h=>⟨by decide,by decide,h⟩) (fun _ _ h=>h)
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
