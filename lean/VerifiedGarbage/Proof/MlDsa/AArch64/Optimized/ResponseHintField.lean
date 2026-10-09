import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintWord
import VerifiedGarbage.Proof.MlDsa.Arith.Zq

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hint_cancel (r c : Zq) : r+c+(-c)=r := by
  apply Fin.ext
  rw [VG.Proof.MlDsa.Arith.val_add',VG.Proof.MlDsa.Arith.val_add',VG.Proof.MlDsa.Arith.val_neg]
  have hr := r.isLt
  have hc := c.isLt
  simp only [q] at *
  omega

theorem hint_makeHint {g : Nat} (hg : IsG g) (r : Zq) (c : Int)
    (hc : -4202495≤c ∧ c≤4210685) :
    makeHint g (-ofInt c) (r+ofInt c)=
      decide (hintPredicate g (lowBits g r+c) (highBits g r)) := by
  unfold makeHint
  rw [hint_cancel]
  simp only [hint_high_change hg r c hc]

theorem hintWord_field {g : Nat} (hg : IsG g) (r : Zq) (raw lo high : BitVec 32)
    (hrl : -8380417<raw.toInt) (hrh : raw.toInt<2*8380417)
    (hl : lo.toInt=lowBits g r) (hh : high.toInt=highBits g r) :
    hintWord (BitVec.ofNat 32 g) (reduceWord raw+lo) high=
      if makeHint g (-ofInt (reduce32 raw.toInt)) (r+ofInt (reduce32 raw.toInt)) then 1 else 0 := by
  have hb := reduce32_bounds (by omega : -2*8380417<raw.toInt) (by omega : raw.toInt<3*8380417)
  have hi := reduceWord_int raw (by omega) (by omega)
  have hlo := lowBits_bounds hg r
  have hgb : 1≤g ∧ g≤524288 := by rcases hg with rfl | rfl <;> decide
  have hadd := addWord_int (reduceWord raw) lo (by rw [hi,hl]; omega) (by rw [hi,hl]; omega)
  have hsum : (reduceWord raw+lo).toInt=lowBits g r+reduce32 raw.toInt := by rw [hadd,hi,hl]; omega
  rw [hintWord_value hgb.1 hgb.2 _ _ (by rw [hsum]; omega) (by rw [hsum]; omega),
    hsum,hh,hint_makeHint hg r _ hb]
  simp only [decide_eq_true_eq]

/-- Reduction changes only the integer representative of the challenge product. -/
theorem reduce32_field (x : Int) : ofInt (reduce32 x)=ofInt x := by
  apply Fin.ext
  have h1 := VG.Proof.MlDsa.KeyGen.ofInt_val (reduce32 x)
  have h2 := VG.Proof.MlDsa.KeyGen.ofInt_val x
  have h3 := reduce32_mod x
  omega

theorem hintWord_raw_field {g : Nat} (hg : IsG g) (r : Zq) (raw lo high : BitVec 32)
    (hrl : -8380417<raw.toInt) (hrh : raw.toInt<2*8380417)
    (hl : lo.toInt=lowBits g r) (hh : high.toInt=highBits g r) :
    hintWord (BitVec.ofNat 32 g) (reduceWord raw+lo) high=
      BitVec.ofNat 32 (makeHint g (-ofInt raw.toInt) (r+ofInt raw.toInt)).toNat := by
  rw [hintWord_field hg r raw lo high hrl hrh hl hh,reduce32_field]
  cases makeHint g (-ofInt raw.toInt) (r+ofInt raw.toInt) <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
