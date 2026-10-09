import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw highWord)

def lowHighWord (g : Nat) (a : BitVec 32) : BitVec 32 :=
  if g==261888 then raw g a &&& 15#32 else highWord g a

theorem lowHighWord_eq {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) : lowHighWord g a=highWord g a := by
  unfold lowHighWord
  split
  · rename_i h
    have he : g=261888 := by simpa using h
    subst g
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (15#32).toNat=2^4-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod,HighPack.raw_toNat hg ha,HighPack.highWord_toNat hg ha]
    rfl
  · rfl

/-- The pipelined high output is the same field decomposition as the scalar schedule. -/
theorem lowHighWord_spec {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) :
    (lowHighWord g a).toNat=(VG.Spec.MlDsa.highBits g ⟨a.toNat,ha⟩).toNat := by
  rw [lowHighWord_eq hg ha,HighPack.highWord_spec hg ha]

/-- The selected lane uses reduce32 after high-bit subtraction. It gives the
same small signed low part as the reference's centered correction. -/
theorem lowReduced_spec {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) :
    (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))).toInt=
      VG.Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ := by
  rw [lowHighWord_eq hg ha]
  have hhigh := HighPack.highWord_toNat hg ha
  have hraw : (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt=
      (a.toNat:Int)-(hbF g a.toNat%hbM g)*(2*g) := by
    have ht := BitVec.toInt_eq_toNat_cond (a-highWord g a*BitVec.ofNat 32 (2*g))
    simp only [BitVec.toNat_sub,BitVec.toNat_mul,BitVec.toNat_ofNat] at ht
    rw [hhigh] at ht
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega
  have hb : -8380417<(a-highWord g a*BitVec.ofNat 32 (2*g)).toInt ∧
      (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt<8380417 := by
    rw [hraw]
    have hr : a.toNat<8380417 := ha
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega
  have hreduce := Response.reduceWord_int (a-highWord g a*BitVec.ofNat 32 (2*g)) (by omega) (by omega)
  rw [hreduce]
  have hrange := reduce32_bounds (x := (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt) (by omega) (by omega)
  have hmod := reduce32_mod (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt
  have hlow := Response.lowBits_centered hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hlrange := Response.lowBits_bounds hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hgsmall : g≤261888 := by rcases hg with rfl | rfl <;> decide
  change Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ = _ at hlow
  rw [← hraw] at hlow
  split at hlow <;> omega

theorem lowReduced_eq {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) :
    Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))=
      Response.lowWord a (HighPack.highWord g a) (BitVec.ofNat 32 (2*g)) := by
  apply BitVec.eq_of_toInt_eq
  rw [lowReduced_spec hg ha,Response.lowWord_spec hg ha]

/-- Semantic low part of the exact signed product-subtraction pipeline. -/
theorem subLowReduced_spec {g : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    let c := Inverse.signCorrected (Response.reduceWord (a-b))
    (Response.reduceWord (c-lowHighWord g c*BitVec.ofNat 32 (2*g))).toInt=
      Spec.MlDsa.lowBits g (Spec.MlDsa.ofInt ((a.toNat:Int)-b.toInt)) := by
  dsimp only
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (Spec.MlDsa.ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowReduced_eq hg cb]
  exact Response.subLow_word hg ha bl bh
end VG.Proof.MlDsa.AArch64.Optimized.Paired
