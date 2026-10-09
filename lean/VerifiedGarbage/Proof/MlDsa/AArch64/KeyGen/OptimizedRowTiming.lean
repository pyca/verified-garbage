import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDotTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPieceTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen

theorem row_relCT {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {i : Nat} (hi : i<p.k)
    (hd : 16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i)
      (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ (i+1))) := by
  have hd' : (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S'/16 :=
    (Nat.le_div_iff_mul_le (by decide : 0<16)).mpr (by simpa only [Nat.mul_comm] using hd)
  simp only [Impl.MlDsa.AArch64.KeyGen.Optimized.row,Code.aarch64Depth,Nat.max_le] at hd'
  have hrem := Nat.div_mul_le_self S' 16
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.row
  exact (dotRow_relCT hF hi).seq
    ((piece_rooted (addS2_piece hP hF hi) (by omega) hP.s64).seq
      ((piece_rooted (p2r_piece hP hF hi) (by omega) hP.s64).seq
        ((piece_rooted (sbp_piece hP hF hi) (by omega) hP.s64).seq
          (piece_rooted (bp_piece hP hF hi) (by omega) hP.s64))))

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
