import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMaskLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun maskMem)

theorem coeffAt_write16_1024 (m : Mem) (p : Addr) {j : Nat} (hj : j+4≤1024)
    (v : BitVec 128) {i : Nat} (hi : i<1024) :
    coeffAt (m.write (coeffAddr p j) 16 v) p i =
      if j≤i ∧ i<j+4 then vword v (i-j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq,show coeffAddr p i=coeffAddr p j+BitVec.ofNat 64 (4*(i-j)) by
      unfold coeffAddr
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4*j+4*(i-j)=4*i by omega]]
    exact readW_write16 _ _ _ (by omega)
  · have hw : m.write (coeffAddr p j) 16 v=m.writeW (coeffAddr p j) v := by
      simp only [Mem.writeW,BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem maskRun_zero {m : Mem} {p : Addr} {n : Nat} (hn : n≤256) :
    ∀i<4*n,coeffAt (maskRun m p 0#128 n) p i=0#32 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rw [maskRun,BoundedFour.maskMem,BitVec.and_zero]
    have hp : p+BitVec.ofNat 64 (16*n)=coeffAddr p (4*n) := by
      unfold coeffAddr
      congr 2
      omega
    rw [hp,coeffAt_write16_1024 _ _ (by omega) _ (by omega)]
    split
    · simp [vword]
    · exact ih (by omega) i (by omega)

theorem maskRun_frame (m : Mem) (p : Addr) (v : BitVec 128) {n N : Nat}
    (hn : n≤4*N) (hN : N≤64) : Frame [⟨p,64*N⟩] m (maskRun m p v n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    unfold maskRun BoundedFour.maskMem
    exact (ih (by omega)).write (List.mem_singleton_self _) _
      (by simpa only [BitVec.add_zero] using (Offset.contains p (d := 16*n) (e := 0) (n := 16) (k := 64*N)
        (by omega) (by omega) (by omega)))

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
