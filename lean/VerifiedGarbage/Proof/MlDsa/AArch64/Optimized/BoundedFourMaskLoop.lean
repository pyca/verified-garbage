import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskStep

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem maskGuard {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) :
    isa.eval (.nonzero .x .x5) s=some (decide (j<64)) := by
  rw [eval_nonzero,hi.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  congr 1
  apply decide_eq_decide.mpr
  have:=hi.bound
  omega

theorem maskLoop_ok {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) (hj : j<64)
    (hr : ∀i<64,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5)) s
      (fun t=>MaskInv σ t p v 64) := by
  refine WP.loop (M := isa) (fun rank s=>∃j,rank=64-j ∧MaskInv σ s p v j ∧j<64)
    ?_ (64-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (maskStep_ok hi hj hr hw) fun t ht=>?_
  have hg:=maskGuard ht
  by_cases hn : j+1<64
  · exact .inr ⟨by rw [hg,decide_eq_true hn],64-(j+1),by omega,j+1,rfl,ht,hn⟩
  · have he : j+1=64 := by omega
    exact .inl ⟨by rw [hg,decide_eq_false hn],by rw [←he]; exact ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
