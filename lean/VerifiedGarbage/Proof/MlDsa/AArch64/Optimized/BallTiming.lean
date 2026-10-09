import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallBranchTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf pub_eq)

 theorem ctWith (v : Proof.Sha3.AArch64.Permutation) (hs : SpongeCursor v.callee)
    (hp : PrefixTiming v.callee) :
    ConstantTime isa sbK.pre sbK.pub (Impl.MlDsa.AArch64.Optimized.Ball.codeWith v.callee) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 sbK.pre sbK.pub fun σ s => s=σ)
    ?_ (fun s₁ s₂ h => ⟨s₁,s₂,h.1,h.2.1,h.2.2,rfl,rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0,.x1,.x3,.x4]
    (fun σ s hp h => by subst h; exact Sample.Ball.pro_ok hp)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      refine ⟨hq.2.2.2.2.2.1,fun r hr => ?_⟩
      rcases mem4 hr with rfl|rfl|rfl|rfl
      exacts [hq.1,hq.2.1,hq.2.2.2.1,hq.2.2.2.2.1]) (by taint_decide)) ?_
  refine RelCT.seq (sponge_step v hs) ?_
  refine RelCT.assoc (RelCT.seq initial_step ?_)
  refine RelCT.seq (branch_step v hp) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr,h₁.env.x25,h₂.env.x25,pub_eq hq]⟩) (by taint_decide)

 theorem sha3_ct : ConstantTime isa sbK.pre sbK.pub
    (Impl.MlDsa.AArch64.Optimized.Ball.codeWith Proof.Sha3.AArch64.Sha3.callee) :=
  ctWith Proof.Sha3.AArch64.Sha3.backend sha3_spongeCursor sha3_prefixTiming
end VG.Proof.MlDsa.AArch64.Optimized.Ball
