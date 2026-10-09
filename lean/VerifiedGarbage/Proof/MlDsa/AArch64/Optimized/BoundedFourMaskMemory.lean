import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Arith.Neon

private theorem write_read (m : Mem) (p : Addr) (n : Nat) : m.write p n (m.read p n)=m := by
  funext x
  unfold Mem.write
  by_cases h : (x-p).toNat<n
  · rw [ite_eq_left h,Mem.extractLsb'_read _ _ h]
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm,BitVec.sub_add_cancel]
  · rw [ite_eq_right h]

theorem maskRun_identity (m : Mem) (p : Addr) (n : Nat) : maskRun m p (~~~0#128) n=m := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [maskRun,ih,maskMem,show (~~~0#128)=BitVec.allOnes 128 from rfl,BitVec.and_allOnes,write_read]

theorem maskRun_zero {m : Mem} {p : Addr} {n : Nat} (hn : n≤64) :
    ∀i<4*n,coeffAt (maskRun m p 0#128 n) p i=0#32 := by
  induction n with
  | zero=>intro i hi; omega
  | succ n ih=>
    intro i hi
    rw [maskRun,maskMem,BitVec.and_zero]
    have hp : p+BitVec.ofNat 64 (16*n)=coeffAddr p (4*n) := by
      unfold coeffAddr
      congr 2
      omega
    rw [hp,coeffAt_write16 _ _ (by omega) _ (by omega)]
    split
    · simp [vword]
    · exact ih (by omega) i (by omega)

theorem maskRun_frame (m : Mem) (p : Addr) (v : BitVec 128) {n : Nat} (hn : n≤64) :
    Frame [polyR p] m (maskRun m p v n) := by
  induction n with
  | zero=>exact Frame.refl _ _
  | succ n ih=>
    unfold maskRun maskMem
    exact (ih (by omega)).write (List.mem_singleton_self _) _
      (by simpa only [BitVec.add_zero] using (Offset.contains p (d := 16*n) (e := 0) (n := 16) (k := 1024)
        (by omega) (by omega) (by decide)))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
