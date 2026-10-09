import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPartition
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowRun_frame (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) {W : List Region} {ro ra : Region} {m : Mem}
    (ho : ro∈W) (ha : ra∈W)
    (hco : ∀i:LowIndex,ro.Contains (out+BitVec.ofNat 64 (lowOff i)) 16 ∧
      ro.Contains (out+BitVec.ofNat 64 (lowOff i+128)) 16)
    (hca : ∀i:LowIndex,ra.Contains (aux+BitVec.ofNat 64 (lowOff i)) 16 ∧
      ra.Contains (aux+BitVec.ofNat 64 (lowOff i+128)) 16)
    (hf : Frame W m d.mem) : Frame W m (lowRun g v out aux c d is).mem := by
  induction is generalizing d with
  | nil => exact hf
  | cons i is ih =>
    simp only [lowRun]
    exact ih _ ((((hf.write ho _ (hco i).1).write ho _ (hco i).2).write ha _ (hca i).1).write ha _ (hca i).2)

def lowPassData (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) : Nat → CheckData
  | 0 => d
  | u+1 =>
    let prev := lowPassData g work out aux c d u
    let v := fun p => Inverse.rawFinalValues (readPair prev.mem (work+BitVec.ofNat 64 (16*u)) 128 p)
    lowRun g v (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c prev allLow

theorem lowPass_frame (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u : Nat} (hu : u≤8) :
    Frame [⟨out,2048⟩,⟨aux,2048⟩] d.mem (lowPassData g work out aux c d u).mem := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [lowPassData]
    refine lowRun_frame _ _ _ _ _ _ _ (ro:=⟨out,2048⟩) (ra:=⟨aux,2048⟩)
      (by simp) (by simp) ?_ ?_ (ih (by omega))
    · intro i
      constructor <;> rw [BitVec.add_assoc,← BitVec.ofNat_add] <;>
        exact Offset.contains_base out (by dsimp only [lowOff]; omega) (by dsimp only [lowOff]; omega)
    · intro i
      constructor <;> rw [BitVec.add_assoc,← BitVec.ofNat_add] <;>
        exact Offset.contains_base aux (by dsimp only [lowOff]; omega) (by dsimp only [lowOff]; omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
