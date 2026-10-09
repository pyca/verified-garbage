import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.Sign

 theorem tail_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {σ s : State}
    (h : IA mlDsa65 D σ 28 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65) s (IA mlDsa65 D σ 30) := by
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
  refine WP.seq (WP.mono (seqR_ok (I:=AS mlDsa65 D σ 28) 2 0
    (fun j _ hj s hs=>WP.mono (slot4_ok (by omega)
      (slotChk_ok mlDsa65 (by simp) 28 (by decide) j (by omega)) hs) fun _ ht=>ht.1)
    s ⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩) fun t ht=>?_)
  exact twoBatch_ok hP (show twoChk mlDsa65 28=true by decide) (by simpa using ht)

 theorem sampleAll65_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {σ s : State}
    (h : IA mlDsa65 D σ 0 s) :
    WP isa (.seq (seqR (sample4 P mlDsa65) 0 7) (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65))
      s (IA mlDsa65 D σ 30) := by
  refine WP.seq (WP.mono (seqR_ok (I:=fun g=>IA mlDsa65 D σ (4*g)) 7 0
    (fun g _ hg s hs=>sample4_ok hP (batchChk_ok mlDsa65 (by simp) g (by change g<7; omega))
      (fun j hj=>slotChk_ok mlDsa65 (by simp) (4*g) (by change 4*g<30; omega) j hj) hs)
    s h) fun t ht=>?_)
  exact tail_ok hP (by simpa using ht)

 theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) (hc : aChk p=true) {σ s : State} (hs : St p D σ s) (h15 : s.gpr .x24=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) s (IA p D σ (p.k*p.ℓ)) := by
  rcases h3 with rfl|rfl|rfl
  · exact Sign.expandA_ok hP (.inl rfl) hc hs h15
  · have hc' := hc
    simp only [aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc'
    obtain ⟨⟨⟨_,hcp⟩,hst⟩,hsk⟩ := hc'
    change WP isa (.seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS)) _) s _
    refine WP.seq (WP.mono (copyP_ok hs.lay hcp) fun s1 ⟨hP1,hcs1,hb⟩=>?_)
    have S1 := hs.step hP1 hst
    have e15 : s1.gpr .x24=1 := by rw [hcs1.get .x24,h15]
    exact sampleAll65_ok hP ⟨S1,by rw [hP1.pa (by decide),hb,rhoOf,←hs.sk,VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15,fun _=>⟨fun _ h=>absurd h (Nat.not_lt_zero _),fun _ h=>absurd h (Nat.not_lt_zero _)⟩,
      fun h0=>absurd (h0.symm.trans e15) (by decide)⟩
  · exact Sign.expandA_ok hP (.inr (.inr rfl)) hc hs h15

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
