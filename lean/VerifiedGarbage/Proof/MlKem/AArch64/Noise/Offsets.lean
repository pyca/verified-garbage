module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Pair

/-! # Noise output bounds and nonoverlap for both layouts -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.Impl.MlKem.AArch64

variable {L : KemLay}

theorem outOff_fits (wf : L.Wf) (room : Room L) (kg : Bool) {j : Nat} (hj : j<2*L.k) :
    outOff L kg j+1024≤L.scl := by
  unfold outOff
  split
  · cases kg <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> lom
  · apply noise_fits room; omega

theorem outOff_low (wf : L.Wf) (room : Room L) (kg : Bool) (j : Nat) :
    (if kg then KG.NS else KEM.NS)+1024≤outOff L kg j := by
  have hkg := noise_past_kg room (j-L.k)
  have hkem := noise_past_kem room (j-L.k)
  cases kg <;> simp only [outOff,Bool.false_eq_true,ite_false,ite_true] <;> split <;> lom

theorem outOff_order (wf : L.Wf) (room : Room L) (kg : Bool) {i j : Nat}
    (hi : i<j) : outOff L kg i+1024≤outOff L kg j := by
  have hkg := noise_past_kg room (j-L.k)
  have hkem := noise_past_kem room (j-L.k)
  cases kg <;> simp only [outOff,Bool.false_eq_true,ite_false,ite_true] <;> split <;> split
  all_goals unfold Impl.MlKem.AArch64.Noise.noiseOff at *; lom

end VG.Proof.MlKem.AArch64.Noise
