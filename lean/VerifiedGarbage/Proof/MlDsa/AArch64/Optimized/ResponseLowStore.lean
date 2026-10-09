import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

theorem lowStep_frame (g B : Nat) (p a l : Addr) {j : Nat} (hj : j<64) (d : LowData) :
    Frame [polyRegion p,polyRegion l] d.mem (lowStep g B p a l j d).mem := by
  have hp : (polyRegion p).Contains (p+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base p (by omega) (by omega)
  have hl : (polyRegion l).Contains (l+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base l (by omega) (by omega)
  exact ((Frame.refl _ _).write (by simp) _ hp).write (by simp) _ hl

theorem coeffAt_write16_other {m : Mem} {p l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (v : BitVec 128) :
    coeffAt (m.write (l+BitVec.ofNat 64 (16*j)) 16 v) p i=coeffAt m p i := by
  have hl : (polyRegion l).Contains (l+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base l (by omega) (by omega)
  have hf : Frame [polyRegion l] m (m.write (l+BitVec.ofNat 64 (16*j)) 16 v) :=
    (Frame.refl _ _).write (by simp) _ hl
  exact coeffAt_frame hf (by intro r hr; simpa using (List.mem_singleton.mp hr ▸ hd)) hi

theorem lowStep_high {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (d : LowData) :
    coeffAt (lowStep g B p a l j d).mem p i=
      if 4*j≤i ∧ i<4*j+4 then HighPack.highWord g (lowInput d.mem p a j (i-4*j))
      else coeffAt d.mem p i := by
  dsimp only [lowStep]
  rw [coeffAt_write16_other hj hi hd]
  have ha : p+BitVec.ofNat 64 (16*j)=coeffAddr p (4*j) := by congr 2; omega
  rw [ha,coeffAt_write16 _ _ (by omega) _ hi]
  split
  · rename_i h; rw [laneVector_word _ (by omega)]
  · rfl

theorem lowStep_low {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (d : LowData) :
    coeffAt (lowStep g B p a l j d).mem l i=
      if 4*j≤i ∧ i<4*j+4 then lowOutput g d.mem p a j (i-4*j)
      else coeffAt d.mem l i := by
  dsimp only [lowStep]
  have ha : l+BitVec.ofNat 64 (16*j)=coeffAddr l (4*j) := by congr 2; omega
  rw [ha,coeffAt_write16 _ _ (by omega) _ hi]
  split
  · rename_i h; rw [laneVector_word _ (by omega)]
  · exact coeffAt_write16_other hj hi hd.symm _

theorem lowRun_frame (m : Mem) (g B : Nat) (p a l : Addr) {j : Nat} (hj : j≤64) :
    Frame [polyRegion p,polyRegion l] m (lowRun m g B p a l j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih => exact (ih (by omega)).trans (lowStep_frame g B p a l (by omega) _)

theorem lowRun_input {m : Mem} {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j≤64) (hi : i<256)
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l)) :
    coeffAt (lowRun m g B p a l j).mem a i=coeffAt m a i := by
  apply coeffAt_frame (lowRun_frame m g B p a l hj) _ hi
  intro r hr
  rcases (show r=polyRegion p ∨ r=polyRegion l by simpa using hr) with rfl|rfl
  · exact hap
  · exact hal

end VG.Proof.MlDsa.AArch64.Optimized.Response
