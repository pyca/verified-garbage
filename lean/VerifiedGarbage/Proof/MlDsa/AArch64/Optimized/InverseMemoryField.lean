import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Lift a resident local bank's arithmetic result into the global polynomial
invariant, preserving all coefficients outside that bank. -/
theorem firstMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} {bound : Int}
    (hu : u<8) (h : SignedPolyIs m p w (-bound) bound)
    (hb : ∀ i : Fin 8, ∀ e<4,
      -bound≤(vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt ∧
      (vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt≤bound)
    (hv : ∀ i : Fin 8, ∀ e<4,
      ofInt (vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.localSlice u) w)[32*u+4*i.val+e]!) :
    SignedPolyIs (firstMemStep m p u) p
      (InverseTraversal.run (InverseTraversal.localSlice u) w) (-bound) bound := by
  constructor
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega)
      rw [he] at hx
      rw [hx]
      exact hb ⟨(k%32)/4,hi⟩ _ (by omega)
    · rw [firstMemStep_outside m p hu hk (by omega)]
      exact h.bound k hk
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega)
      rw [he] at hx
      rw [hx]
      simpa only [he] using hv ⟨(k%32)/4,hi⟩ (k%4) (by omega)
    · rw [firstMemStep_outside m p hu hk (by omega),h.value k hk,
        InverseTraversal.run_outside _ _ _ (InverseTraversal.local_supported ⟨u,hu⟩) w hk hs]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
