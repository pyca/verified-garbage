module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixFrame

/-! # Advance the existing key-generation matrix invariant by a pair -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

theorem BInvW.paired {w16 : Bool} {s₀ s t : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : BInvW w16 P s₀ e s)
    (ht : Paired.PairOutcomeW w16
      (matSeed (rhoK P s₀) (e/P.k) (e%P.k))
      (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))
      (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) s t) :
    BInvW w16 P s₀ (e+2) t := by
  have hw := hp.wf
  have fr : Frame (pairWrites s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := pair_far hp he (b:=3) (o:=AH+1024*i) (l:=1024)
    (by decide) (by simp only [kL]; lom) (.inr (by lom))
  refine ⟨pair_kb hp he h.kb ht.keep fr,?_,?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (pair_far hp he (by decide) (by kl) (.inr (by lom))) (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (pair_far hp he (by decide) (by kl) (.inr (by lom))) (by decide)]
    exact h.sig
  · have hall : allOk P s₀ (e+2) ↔ (allOk P s₀ e ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome) ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))).isSome := by
      rw [show e+2=(e+1)+1 by omega,allOk_succ,allOk_succ]
    rw [ht.status,h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro i hi
    rcases (by omega : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · rw [aAtW,polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

theorem BInvW.singleton {w16 : Bool} {s₀ s t : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : BInvW w16 P s₀ e s)
    (ht : Paired.LastOutcomeW w16 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))
      (kA s₀ 3+BitVec.ofNat 64 SS) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) s t) :
    BInvW w16 P s₀ (e+1) t := by
  have hw := hp.wf
  have fr : Frame (lastWrites s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := last_far hp he (b:=3) (o:=AH+1024*i) (l:=1024)
    (by decide) (by simp only [kL]; lom) (.inr (by lom))
  refine ⟨last_kb hp he h.kb ht.keep fr,?_,?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (last_far hp he (by decide) (by kl) (.inr (by lom))) (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (last_far hp he (by decide) (by kl) (.inr (by lom))) (by decide)]
    exact h.sig
  · rw [ht.status,h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome <;>
      simp [allOk_succ,ha,hb]
  · intro i hi
    rcases (by omega : i<e ∨ i=e) with hi|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reduced
  · intro i hi
    rcases (by omega : i<e ∨ i=e) with hi|rfl
    · rw [aAtW,polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.result

end VG.Proof.MlKem.AArch64.KeyGen
