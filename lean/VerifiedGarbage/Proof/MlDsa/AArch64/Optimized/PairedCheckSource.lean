import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Earlier z/h output writes leave the raw inverse source unchanged. -/
theorem finalPass_readPair (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u k : Nat} (hu : u≤8) (hk : k<8)
    (hd : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    readPair (finalPassData hint work out aux c d u).mem (work+BitVec.ofNat 64 (16*k)) 128 =
      readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 := by
  exact readPair_workFrame hk (finalPass_frame hint work out aux c d hu)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd)

/-- Earlier r0 writes to either output leave the raw inverse source unchanged. -/
theorem lowPass_readPair (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u k : Nat} (hu : u≤8) (hk : k<8)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    readPair (lowPassData g work out aux c d u).mem (work+BitVec.ofNat 64 (16*k)) 128 =
      readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 := by
  exact readPair_workFrame hk (lowPass_frame g work out aux c d hu)
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl <;> with_reducible assumption)

/-- Each z/h iteration uses the same original transform result. -/
theorem finalPass_step (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u : Nat} (hu : u<8)
    (hd : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    finalPassData hint work out aux c d (u+1)=
      checkRun hint (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*u)) 128 p))
        (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c
        (finalPassData hint work out aux c d u) allChecks := by
  rw [finalPassData,finalPass_readPair hint work out aux c d (by omega) hu hd]

theorem lowPass_step (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u : Nat} (hu : u<8)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    lowPassData g work out aux c d (u+1)=
      lowRun g (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*u)) 128 p))
        (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c
        (lowPassData g work out aux c d u) allLow := by
  rw [lowPassData,lowPass_readPair g work out aux c d (by omega) hu ho ha]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
