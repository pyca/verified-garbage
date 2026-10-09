import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeLoopStep

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem squeezeGuard {σ s : State} {c : SqueezeCfg} {A : Nat→Spec.Sha3.State} {j : Nat}
    (hi : SqueezeInv σ s c A j) :
    isa.eval (.nonzero .x .x28) s=some (decide (j<2)) := by
  rw [eval_nonzero,hi.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  congr 1
  apply decide_eq_decide.mpr
  have:=hi.bound
  omega

theorem squeezeLoop_ok (sha3 : Bool) {σ s : State} {c : SqueezeCfg}
    {A : Nat→Spec.Sha3.State} {j : Nat} (hl : SqueezeLayout σ c)
    (hi : SqueezeInv σ s c A j) (hj : j<2) :
    WP isa (.loop (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep sha3) (.nonzero .x .x28)) s
      (fun t=>SqueezeInv σ t c A 2) := by
  refine WP.loop (M := isa) (fun rank s=>∃j,rank=2-j ∧ SqueezeInv σ s c A j ∧j<2)
    ?_ (2-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (squeezeLoopStep_ok sha3 hl hi hj) fun t ht=>?_
  have hg:=squeezeGuard ht
  by_cases hn : j+1<2
  · exact .inr ⟨by rw [hg,decide_eq_true hn],2-(j+1),by omega,j+1,rfl,ht,hn⟩
  · have he : j+1=2 := by omega
    exact .inl ⟨by rw [hg,decide_eq_false hn],by rw [←he]; exact ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
