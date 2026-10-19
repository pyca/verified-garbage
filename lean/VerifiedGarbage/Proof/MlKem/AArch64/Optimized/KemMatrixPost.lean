module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixFrame
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastSpecPost

/-! # Advance the encryption matrix invariant by pairs and the odd final entry -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

theorem BInvW.paired {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : Paired.PairOutcomeW w16 (matSeed ρ (e/P.k) (e%P.k)) (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))
      (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) s t) :
    BInvW w16 P L s₀ mA ρ (e+2) t := by
  have hw := hp.wf
  have fr : Frame (pairWrites L s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := pair_far hp he (o:=AH+1024*i) (l:=1024)
    (by lom) (by constructor <;> lom)
  refine ⟨pair_kb hp he h.kb ht.keep fr,h.fr.trans (fr.sub (pair_sub he)),?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (pair_far hp he (o := SB) (l := 32) (by lom) (by constructor <;> lom)) (by decide)]
    exact h.rho
  · have hall : okR P ρ (e+2) ↔ (okR P ρ e ∧ (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome) ∧
        (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome := by
      rw [show e+2=(e+1)+1 by omega,okR_succ,okR_succ]
    rw [ht.status,h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro i hi
    rcases (by omega : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · rw [polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

theorem BInvW.singleton {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : Paired.LastOutcomeW w16 (matSeed ρ (e/P.k) (e%P.k)) (sA L s₀ SS) (aP L s₀ e) s t) :
    BInvW w16 P L s₀ mA ρ (e+1) t := by
  have hw := hp.wf
  have fr : Frame (lastWrites L s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := last_far hp he (o:=AH+1024*i) (l:=1024)
    (by lom) (by constructor <;> lom)
  refine ⟨last_kb hp he h.kb ht.keep fr,h.fr.trans (fr.sub (last_sub he)),?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (last_far hp he (o := SB) (l := 32) (by lom) (by constructor <;> lom)) (by decide)]
    exact h.rho
  · rw [ht.status,h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome <;>
      simp [okR_succ,ha,hb]
  · intro i hi
    rcases (by omega : i<e ∨ i=e) with hi|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reduced
  · intro i hi
    rcases (by omega : i<e ∨ i=e) with hi|rfl
    · rw [polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.result

end VG.Proof.MlKem.AArch64.Kem
