import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round

theorem centeredCorrection_int {l : BitVec 32} (hl : -8380417<l.toInt) (hh : l.toInt<8380417) :
    (l-((4190208#32-l).sshiftRight 31 &&& 8380417#32)).toInt=
      l.toInt-(if 4190208<l.toInt then 8380417 else 0) := by
  have ht := BitVec.toInt_eq_toNat_cond (4190208#32-l)
  have hd : (4190208#32-l).toInt=4190208-l.toInt :=
    subWord_int _ _ (by change -2147483648≤4190208-l.toInt; omega)
      (by change 4190208-l.toInt<2147483648; omega)
  rw [ResidentMask.signMask32]
  by_cases h : 4190208<l.toInt
  · rw [ite_eq_right (by omega),ite_eq_left h]
    rw [show (-1:BitVec 32) &&& 8380417#32=8380417#32 by decide]
    exact subWord_int _ _ (by change -2147483648≤l.toInt-8380417; omega)
      (by change l.toInt-8380417<2147483648; omega)
  · rw [ite_eq_left (by omega),ite_eq_right h]
    simp

theorem lowWord_spec {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat<q) :
    (lowWord a (HighPack.highWord g a) (BitVec.ofNat 32 (2*g))).toInt=
      lowBits g ⟨a.toNat,ha⟩ := by
  have hhigh := HighPack.highWord_toNat hg ha
  have hraw : (a-HighPack.highWord g a*BitVec.ofNat 32 (2*g)).toInt=
      (a.toNat:Int)-(VG.Proof.MlDsa.Round.hbF g a.toNat%hbM g)*(2*g) := by
    have ht := BitVec.toInt_eq_toNat_cond (a-HighPack.highWord g a*BitVec.ofNat 32 (2*g))
    simp only [BitVec.toNat_sub,BitVec.toNat_mul,BitVec.toNat_ofNat] at ht
    rw [hhigh] at ht
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] at * <;> omega
  have hb : -8380417<(a-HighPack.highWord g a*BitVec.ofNat 32 (2*g)).toInt ∧
      (a-HighPack.highWord g a*BitVec.ofNat 32 (2*g)).toInt<8380417 := by
    rw [hraw]
    have hr : a.toNat<8380417 := ha
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] at * <;> omega
  rw [lowWord,centeredCorrection_int hb.1 hb.2,hraw,lowBits_centered hg]

theorem subInput_word {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (Inverse.signCorrected (reduceWord (a-b))).toNat=(ofInt ((a.toNat:Int)-b.toInt)).val := by
  have hat := BitVec.toInt_eq_toNat_cond a
  have ha' : a.toNat<8380417 := ha
  have hai : a.toInt=(a.toNat:Int) := by omega
  have hab := subWord_int a b (by rw [hai]; omega) (by rw [hai]; omega)
  rw [hai] at hab
  rw [reduce_signCorrected (by rw [hab]; omega) (by rw [hab]; omega),hab]

theorem subLow_word {g : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    let c := Inverse.signCorrected (reduceWord (a-b))
    (lowWord c (HighPack.highWord g c) (BitVec.ofNat 32 (2*g))).toInt=
      lowBits g (ofInt ((a.toNat:Int)-b.toInt)) := by
  dsimp only
  have hc := subInput_word ha bl bh
  have cb : (Inverse.signCorrected (reduceWord (a-b))).toNat<q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowWord_spec hg cb]
  congr 1
  exact Fin.ext hc

theorem subHigh_word {g : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (HighPack.highWord g (Inverse.signCorrected (reduceWord (a-b)))).toNat=
      (highBits g (ofInt ((a.toNat:Int)-b.toInt))).toNat := by
  have hc := subInput_word ha bl bh
  have cb : (Inverse.signCorrected (reduceWord (a-b))).toNat<q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [HighPack.highWord_spec hg cb]
  congr 2
  exact Fin.ext hc

theorem subLow_norm {g B : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    let c := Inverse.signCorrected (reduceWord (a-b))
    normMask (lowWord c (HighPack.highWord g c) (BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B then 0 else -1 := by
  dsimp only
  have hi := subLow_word hg ha bl bh
  have hbnd := lowBits_bounds hg (ofInt ((a.toNat:Int)-b.toInt))
  have hg' : g≤261888 := by rcases hg with rfl | rfl <;> decide
  rw [normMask_value (hB:=hB) (hB':=hB') (by rw [hi]; omega) (by rw [hi]; omega),hi]
  have hn := reduced_norm_iff (lowBits g (ofInt ((a.toNat:Int)-b.toInt))) B (by omega) (by omega) hB'
  by_cases h : normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B
  · rw [ite_eq_left h,ite_eq_left (hn.mp h)]
  · rw [ite_eq_right h,ite_eq_right (fun he => h (hn.mpr he))]

end VG.Proof.MlDsa.AArch64.Optimized.Response
