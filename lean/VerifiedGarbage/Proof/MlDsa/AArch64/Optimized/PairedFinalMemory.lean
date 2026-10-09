import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalAdvance
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem checkRun_frame (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) {W : List Region} {r : Region}
    {m : Mem} (hr : r∈W)
    (hc : ∀p:Fin 2,∀j:Fin 8,r.Contains (out+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hf : Frame W m d.mem) : Frame W m (checkRun hint v out aux c d js).mem := by
  induction js generalizing d with
  | nil => exact hf
  | cons op js ih =>
    simp only [checkRun]
    exact ih _ (hf.write hr _ (hc op.1 op.2))

def finalPassData (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) : Nat → CheckData
  | 0 => d
  | u+1 =>
    let prev := finalPassData hint work out aux c d u
    let v := fun p => Inverse.rawFinalValues (readPair prev.mem (work+BitVec.ofNat 64 (16*u)) 128 p)
    checkRun hint v (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c prev allChecks

theorem finalPass_frame (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u : Nat} (hu : u≤8) :
    Frame [⟨out,2048⟩] d.mem (finalPassData hint work out aux c d u).mem := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [finalPassData]
    refine checkRun_frame _ _ _ _ _ _ _ (r:=⟨out,2048⟩) (by simp) ?_ (ih (by omega))
    intro p j
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base out (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
