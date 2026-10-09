import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFixedTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

 theorem env_relCT {v : Nat} {σ τ : State} {P Q R S : State → Prop} {c : Prog isa}
    (pub : Pub v σ τ) (hs : ∀s,P s → Env v σ s) (ht : ∀s,Q s → Env v τ s)
    (hc : PointerCT [.x19] c) (ws : ∀s,P s → WP isa c s R)
    (wt : ∀t,Q t → WP isa c t S) :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => R s ∧ S t) := by
  have ct : RelCT isa (fun s t => P s ∧ Q t) c (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have se := hs s h.1
    have te := ht t h.2
    have ha : VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]) s t := by
      refine ⟨se.sp.trans (pub.2.2.2.1.trans te.sp.symm),?_⟩
      simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton]
      intro r hr
      subst r
      rw [se.x19,te.x19,pub.2.2.1]
    exact ⟨hc s t tr ur s' t' True.intro True.intro ha es et,True.intro⟩
  exact (ct.wp (fun s t h => ⟨ws s h.1,wt t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
