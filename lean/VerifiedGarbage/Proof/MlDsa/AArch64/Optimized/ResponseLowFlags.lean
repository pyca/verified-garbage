import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def lowBad (m : Mem) (g : Nat) (p a : Addr) (B j e : Nat) : Bool :=
  decide (B≤normZq (ofInt (lowBits g (ofInt
    (((coeffAt m p (4*j+e)).toNat:Int)-(coeffAt m a (4*j+e)).toInt)))))

theorem lowOutput_current (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {j e : Nat} (hj : j<64) (he : e<4) :
    lowOutput g (lowRun m g B p a l j).mem p a j e=lowSigned m g p a (4*j+e) := by
  rw [lowOutput_coeff _ _ _ _ _ he]
  simp only [lowSigned,lowHigh,lowCanonical]
  rw [(lowRun_prefix m g B p a l hpl hap hal (by omega)).1 _ (by omega),ite_eq_right (by omega),
    lowRun_input (by omega) (by omega) hap hal]

theorem lowSigned_mask {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (m : Mem) (p a : Addr) (i : Nat) (ha : (coeffAt m p i).toNat<8380417)
    (hb : -8380417<(coeffAt m a i).toInt ∧ (coeffAt m a i).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    normMask (lowSigned m g p a i) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      maskWord (decide (B≤normZq (ofInt (lowBits g (ofInt (((coeffAt m p i).toNat:Int)-(coeffAt m a i).toInt)))))) := by
  rw [lowSigned,lowHigh,lowCanonical,subLow_norm hg ha hb.1 hb.2 hB hB']
  unfold maskWord
  split <;> rename_i h
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

theorem lowRun_flags (m : Mem) (g B : Nat) (p a l : Addr)
    (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    (hB : 1≤B) (hB' : B≤524288)
    (ha : ∀i<256,(coeffAt m p i).toNat<8380417)
    (hb : ∀i<256,-8380417<(coeffAt m a i).toInt ∧ (coeffAt m a i).toInt<2*8380417)
    {j : Nat} (hj : j≤64) :
    ∀e<4,vword (lowRun m g B p a l j).flags e=maskWord (flagBad (lowBad m g p a B) j e) := by
  induction j with
  | zero => intro e he; simp [lowRun,flagBad,maskWord,vword]
  | succ j ih =>
    intro e he
    rw [lowRun]
    simp only [lowStep,laneVector_word _ he]
    rw [ih (by omega) e he,lowOutput_current m g B p a l hpl hap hal (by omega) he,
      lowSigned_mask hg m p a _ (ha _ (by omega)) (hb _ (by omega)) hB hB',maskWord_or]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
