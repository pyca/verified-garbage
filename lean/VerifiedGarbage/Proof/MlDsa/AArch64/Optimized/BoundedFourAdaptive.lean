import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRunFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem SamplerRun.congr {σ s : State} {A : Nat→Spec.Sha3.State} {L K : Nat→List Zq}
    (h : SamplerRun σ s A L) (he : ∀i<4,L i=K i) : SamplerRun σ s A K := by
  refine ⟨h.env,h.pair0,h.pair1,h.table,⟨?_,?_,?_⟩⟩
  · intro i hi; rw [←he i hi]; exact h.fields.bound i hi
  · intro i hi; rw [←he i hi]; exact h.fields.stored i hi
  · intro i hi; rw [←he i hi]; exact h.fields.count i hi

theorem countFlag_congr {L K : Nat→List Zq} (he : ∀i<4,L i=K i) : countFlag L=countFlag K := by
  unfold countFlag foldedFlags
  change ((BitVec.ofNat 64 (256-(L 0).length)|||BitVec.ofNat 64 (256-(L 1).length))|||
    BitVec.ofNat 64 (256-(L 2).length))|||BitVec.ofNat 64 (256-(L 3).length)=_
  rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]
  rfl

def secondBatch (sha3 : Bool) (η : Nat) : Prog isa :=
 .ite (.zero .x .x27) (.block [])
  (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 272)
   (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η 272)
    (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags)))

theorem secondBatch_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ s : State}
    (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State} {L : Nat→List Zq}
    (hs : SamplerRun σ s A L) (hflag : s.gpr .x27=countFlag L) :
    WP isa (secondBatch sha3 η) s fun t=>
      ∃A',SamplerRun σ t A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        t.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i))) := by
  unfold secondBatch
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _=>?_) (by simp)
    have hfull := (countFlag_zero hs.fields.bound).mp (hflag.symm.trans hz)
    have he : ∀i<4,L i=rbFold η (L i) (chunkBytes (A i)) := fun i hi=>
      (rbFold_full (hfull i hi) _).symm
    exact WP.block_nil_iff.mpr ⟨A,hs.congr he,hflag.trans (countFlag_congr he)⟩
  · refine WP.ite false (by rw [eval_zero,show (s.gpr .x27 == 0)=false from beq_eq_false_iff_ne.mpr hz])
      (by simp) (fun _=>?_)
    have hc:=WP.seq (WP.mono (sampleRound_ok sha3 hη hp hs (by decide : 272≤272)) fun t ht=>
      WP.mono (flagsStage_ok hp ht) fun u ⟨hu,hf⟩=>
        (show ∃A',SamplerRun σ u A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
          u.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i))) from ⟨_,hu,hf⟩))
    simpa only [WP.seq_iff (M := isa)] using hc

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
