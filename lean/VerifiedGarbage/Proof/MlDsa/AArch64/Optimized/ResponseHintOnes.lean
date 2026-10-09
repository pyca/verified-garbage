import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked
import VerifiedGarbage.Proof.MlDsa.Round.Ones

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem hintAt_original (m : Mem) (B : BitVec 32) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) (hh : (pR p).Disjoint (pR h))
    {j e : Nat} (hj : j<64) (he : e<4) :
    hintAt B (hintRun m B p a h j).mem p a h j e=
      hintWord B (reduceWord (coeffAt m a (4*j+e))+coeffAt m p (4*j+e)) (coeffAt m h (4*j+e)) := by
  rw [hintAt_coeff _ _ _ _ _ _ he,
    hintRun_prefix m p a h B hd hh (by omega) (4*j+e) (by omega),ite_eq_right (by omega)]
  have fa := coeffAt_frame (hintRun_frame m p a h B (j:=j) (by omega))
    (by simpa using hd.symm) (show 4*j+e<n by change 4*j+e<256; omega)
  have fh := coeffAt_frame (hintRun_frame m p a h B (j:=j) (by omega))
    (by simpa using hh.symm) (show 4*j+e<n by change 4*j+e<256; omega)
  rw [fa,fh]

theorem hintCount_next (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat) :
    hintCount m B p a h (j+1)=hintCount m B p a h j+
      (hintAt B (hintRun m B p a h j).mem p a h j 0).toNat+
      (hintAt B (hintRun m B p a h j).mem p a h j 1).toNat+
      (hintAt B (hintRun m B p a h j).mem p a h j 2).toNat+
      (hintAt B (hintRun m B p a h j).mem p a h j 3).toNat := by
  simp only [hintCount,hintLaneCount]
  omega

theorem hintCount_ones (m : Mem) (B : BitVec 32) (p a h : Addr) (out : Vector Bool n)
    (hd : (pR p).Disjoint (pR a)) (hh : (pR p).Disjoint (pR h))
    (ho : ∀k<256,(hintWord B (reduceWord (coeffAt m a k)+coeffAt m p k) (coeffAt m h k)).toNat=out[k]!.toNat) :
    hintCount m B p a h 64=hintOnes [out] := by
  have hi : ∀j≤64,hintCount m B p a h j=VG.Proof.MlDsa.Round.onesTo out (4*j) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [hintCount_next,ih (by omega)]
      have lane (e : Nat) (he : e<4) :
          (hintAt B (hintRun m B p a h j).mem p a h j e).toNat=out[4*j+e]!.toNat := by
        rw [hintAt_original m B p a h hd hh (by omega) he,ho _ (by omega)]
      rw [lane 0 (by decide),lane 1 (by decide),lane 2 (by decide),lane 3 (by decide)]
      rw [show 4*(j+1)=((4*j+1)+1)+1+1 by omega]
      rw [VG.Proof.MlDsa.Round.onesTo_succ,VG.Proof.MlDsa.Round.onesTo_succ,
        VG.Proof.MlDsa.Round.onesTo_succ,VG.Proof.MlDsa.Round.onesTo_succ]
      simp only [Nat.add_zero]
  rw [hi 64 (by decide),VG.Proof.MlDsa.Round.hintOnes_onesTo]

end VG.Proof.MlDsa.AArch64.Optimized.Response
