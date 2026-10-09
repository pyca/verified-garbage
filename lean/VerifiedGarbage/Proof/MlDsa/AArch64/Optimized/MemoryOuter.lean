import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Memory supplies the strided bank's field interpretation. -/
theorem readBank_outer_field {m : Mem} {p : Addr} {w : Poly} {lo hi : Int}
    (h : SignedPolyIs m p w lo hi) {u : Nat} (hu : u<8) :
    BankField u (readBank m (coeffAddr p (4*u)) 128) w := by
  intro i e he
  rw [readBank_coeff m p (4*u) 32 i he]
  have hi : 4*u+32*i.val+e<n := by change 4*u+32*i.val+e<256; omega
  simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h.value _ hi

/-- One complete strided slice advances the global field schedule without
changing any coefficient outside that slice. -/
theorem outerMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} (hu : u<8)
    (h : SignedPolyIs m p w (-(15*8380417)) (15*8380417))
    (hb : BankBound (readBank m (coeffAddr p (4*u)) 128) 8380417) :
    SignedPolyIs (outerMemStep m (coeffAddr p (4*u)) (fun k => (zetaNat k : Int))) p
      (Traversal.run (Traversal.outerSlice u) w) (-(15*8380417)) (15*8380417) := by
  have hc := outerThree_field _ w hu hb (readBank_outer_field h hu)
  have bound : 4*u+32*7+4≤256 := by omega
  have atCoeff (k : Nat) (hk : k<n) (hu' : k%32/4=u) :
      coeffAt (outerMemStep m (coeffAddr p (4*u)) (fun k => (zetaNat k : Int))) p k =
      vword (outerValues (readBank m (coeffAddr p (4*u)) 128)
        (fun k => (zetaNat k : Int)) outerSteps)[k/32]! (k%4) := by
    have hi : k/32<8 := by change k<256 at hk; omega
    have he : k=4*u+32*(k/32)+k%4 := by omega
    unfold outerMemStep
    have hh := writeBank_coeff_at
      (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps)
      m p (by decide : 4≤32) bound ⟨k/32,hi⟩ (e := k%4) (by omega)
    rw [← he] at hh
    simpa only [getElem!_pos (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps) (k/32) hi] using hh
  have outside (k : Nat) (hk : k<n) (hu' : k%32/4≠u) :
      coeffAt (outerMemStep m (coeffAddr p (4*u)) (fun k => (zetaNat k : Int))) p k=coeffAt m p k := by
    unfold outerMemStep
    apply writeBank_coeff_outside (step := 32) (start := 4*u) _ _ _ bound hk
    intro i
    omega
  constructor
  · intro k hk
    by_cases hu' : k%32/4=u
    · rw [atCoeff k hk hu']
      have hi : k/32<8 := by change k<256 at hk; omega
      simpa only [getElem!_pos (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps) (k/32) hi] using hc.1 ⟨k/32,hi⟩ (k%4) (by omega)
    · rw [outside k hk hu']; exact h.bound k hk
  · intro k hk
    by_cases hu' : k%32/4=u
    · rw [atCoeff k hk hu']
      have hi : k/32<8 := by change k<256 at hk; omega
      have he : Traversal.loc u (k/32) (k%4)=k := by unfold Traversal.loc; omega
      simpa only [getElem!_pos (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps) (k/32) hi,he] using hc.2 ⟨k/32,hi⟩ (k%4) (by omega)
    · rw [outside k hk hu',h.value k hk,
        Traversal.run_outside _ _ _ (Traversal.outer_supported ⟨u,hu⟩) w hk hu']

end VG.Proof.MlDsa.AArch64.Optimized
