import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatchTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

 def firstChecks (k : Nat) (hk : k<4) : SegmentChecks k 0 168 := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

 def secondChecks (k : Nat) (hk : k<4) : SegmentChecks k 504 112 := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

 def lastChecks (k : Nat) (hk : k<4) : SegmentChecks k 840 56 := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
