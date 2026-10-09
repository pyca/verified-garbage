import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFinish
import VerifiedGarbage.Proof.MlDsa.Sample.Rej4
import VerifiedGarbage.Spec.MlDsa.RejNTT2

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

def Outcome (v : Nat) (σ t : State) : Prop :=
  let r := (t.gpr .x0).setWidth 32
  (r=1 → ∀k<v,Spec.MlDsa.Reduced t.mem (Spec.MlDsa.poly4 (aP σ) k)) ∧
    ((r=1 ∧ ∀k<v,∃b : Spec.MlDsa.Bounds,Spec.MlDsa.rejNTTPoly b.rejNTT
      (Spec.MlDsa.seed4 σ.mem (seedP σ) k)=some (Spec.MlDsa.polyAt t.mem (Spec.MlDsa.poly4 (aP σ) k))) ∨
     (r=0 ∧ ∃k<v,Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
      (Spec.MlDsa.seed4 σ.mem (seedP σ) k)=none))

theorem prefixRow_spec (σ : State) (k : Nat) :
    prefixRow σ k 1008=rnFold [] (Spec.MlDsa.G (Spec.MlDsa.seed4 σ.mem (seedP σ) k) 1008) := by
  unfold prefixRow
  rw [streamBytes_full]

theorem Result.outcome {v : Nat} {σ t : State} (h : Result v σ t) : Outcome v σ t := by
  unfold Outcome
  by_cases hall : ∀k<v,(prefixRow σ k 1008).length=256
  · have hr : (t.gpr .x0).setWidth 32=1 := by rw [h.status,ite_eq_left hall]; rfl
    have hp : ∀k<v,Spec.MlDsa.PolyIs t.mem (polyP σ k) (toPoly (prefixRow σ k 1008)) :=
      fun k hk => stored_polyIs (h.stored k hk) (hall k hk)
    refine ⟨fun _ k hk => (hp k hk).1,.inl ⟨hr,fun k hk =>
      ⟨{Spec.MlDsa.minBounds with rejNTT := 1008},?_⟩⟩⟩
    have hs := hall k hk
    rw [prefixRow_spec] at hs
    rw [rejNTT_some hs]
    exact congrArg some (by
      rw [← prefixRow_spec]
      exact (hp k hk).2.symm)
  · have hr : (t.gpr .x0).setWidth 32=0 := by rw [h.status,ite_eq_right hall]; rfl
    refine ⟨fun hh => absurd (hr.symm.trans hh) (by decide),.inr ⟨hr,?_⟩⟩
    simp only [Classical.not_forall] at hall
    obtain ⟨k,hk,hbad⟩ := hall
    refine ⟨k,hk,rejNTT_none (B := 1008) (by decide) (by decide) ?_⟩
    simpa only [prefixRow_spec] using hbad

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
